"""Change z and restore all directional budgets by mixing with the zero field."""
import argparse
import json
import sys
import tempfile
from fractions import Fraction as F
from math import ceil, floor
from pathlib import Path
from zipfile import ZipFile

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
from diagnostics import BASE,enclosure
from poisson_fourier import integrals,log_interval,pi_interval


def net_threshold(D,K,A,lam):
    def test(C):
        t=D/C
        return K*((1-t)**2+t*t)+lam*t-A
    unit=10**9
    low,high=ceil(3*D*unit),ceil(6*D*unit)
    while test(F(high,unit))<=0:
        high*=2
    assert test(F(low,unit))<0
    while high-low>1:
        m=(low+high)//2
        if test(F(m,unit))>0:high=m
        else:low=m
    C=F(high,unit)
    t=D/C
    b=C/(2*K*(1-2*t)-lam)
    assert b>0 and 3*C+b*lam>2*b*K and C+b*lam<2*b*K
    return [low-unit,high-unit],b


def calculate(d,design,pool,tab,con,fee,scalar):
    L,D,G,s,A0=(F(con[k]) for k in ("L","D","G","s","A0"))
    raw=design["a"]
    a=[L*r/(2*sum(raw)-raw[0]) for r in raw[:0:-1]+raw]
    widths=[F(w,10000) for w in design["even"]]
    last=F(0)
    moments=[]
    for i in range(len(raw)-1,0,-1):
        need=sum(a[len(raw)-1+i:])
        for k in range(1,len(widths)+1):
            x=(sum(widths[:k])-need)/k
            if (widths[k] if k<len(widths) else 0)<=x<=widths[k-1]:
                break
        assert sum(max(0,w-x) for w in widths)==need
        area=sum(max(0,w*w-x*x) for w in widths)/2
        moments.append(area-last)
        last=area
    moments=moments[::-1]
    Q=2*sum(i*v for i,v in enumerate(moments,1))/L
    assert Q==F(con["Q"])
    model=scalar(d,[design["even"]]*4,a)
    U={tag:model.bounds(row,0,[])[0] for tag,row in pool["ordinary"].items()}
    P={tag:model.bounds(row,fee[tag],[])[0] for tag,row in pool["tilted"].items()}
    assert "scalar-0" not in fee
    zero=U["scalar-0"]
    fields={tag:[F(v,100000) for v in row["field"]] for tag,row in pool["ordinary"].items()}
    assert not any(fields["scalar-0"])
    pi_lo,pi_hi=pi_interval()
    rows=[]
    for delta in ("-0.005","-0.001","-0.0001","0","0.000001","0.0001","0.001","0.005"):
        z=F(design["z"])+F(delta)
        Klo,Khi=log_interval(1/z)
        cap=(1/z-z)/4
        W,lam=F(0),F(0)
        spends=[F(0)]*len(moments)
        for l,r,mix in tab["allocation"]:
            w0,j0=integrals(z,F(l,tab["grid"]))
            w1,j1=integrals(z,F(r,tab["grid"]))
            wl,wh=w1[0]-w0[1],w1[1]-w0[0]
            jl,jh=j1[0]-j0[1],j1[1]-j0[0]
            for tag,n in mix:
                k=fields[tag];fraction=F(n,tab["unit"])
                first=(U[tag]+P.get(tag,U[tag]))/2
                second=-2*sum(v*x for v,x in zip(k[1:],moments))/L
                W+=fraction*(max(first*wl,first*wh)+max(second*jl,second*jh))
                lam+=fraction*wl*F(fee.get(tag,0),2*10**7)
                for i in range(len(spends)):
                    dx=k[i+1]-k[i]
                    spends[i]+=fraction*max(dx*jl,dx*jh)
        scale=min(F(1),(pi_lo*cap-F(1,10**12))/max(spends))
        assert 0<scale<=1 and all(scale*x<pi_lo*cap for x in spends)
        boundary=pi_hi*cap*Q+scale*W+(1-scale)*zero
        A=d*(A0+G)+(d-1)*zero+Khi*s+boundary
        K=Klo*L/2
        threshold,b=net_threshold(D,K,A,scale*lam)
        C=F(threshold[-1],10**9)+1
        h=(d-1)/(b*L)
        assert 0<h<1 and 3*(C-d+1)+b*scale*lam>2*b*K and A0+G+zero>0
        gamma=F(1,2)-s/L-pi_hi*Q/(2*L*(1-h*h))
        loss=(2*b*K-C+d-1-b*scale*lam)/(4*b*K)
        assert gamma>loss
        rows.append(dict(delta=delta,z=str(z),zero_field_added_x1e12=enclosure(1-scale),
                         threshold_x1e9=threshold,secondary_slack_x1e12=enclosure(gamma-loss)))
    return rows


def verify():
    out={}
    with tempfile.TemporaryDirectory() as temp, ZipFile(BASE) as archive:
        archive.extractall(temp)
        sys.path.insert(0,temp)
        from scalar import Scalar
        def read(name):
            return json.loads(archive.read(name))
        for case in read("certificate.json")["cases"]:
            d=case["d"]
            out[str(d)]=calculate(d,read(f"balanced{d}.json"),read(f"final-fields{d}.json"),read(f"angles{d}.json"),
                                   case["balanced"]["constants"],read(f"prior/center{d}.json")["price"],Scalar)
    return out


if __name__=="__main__":
    if not __debug__:
        raise RuntimeError("Enable assertions")
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json",type=Path)
    args=parser.parse_args()
    out=verify()
    if args.json:args.json.write_text(json.dumps(out,indent=2)+"\n",encoding="utf-8")
    for d,rows in out.items():
        print(d,[(r["delta"],r["threshold_x1e9"]) for r in rows],flush=True)

