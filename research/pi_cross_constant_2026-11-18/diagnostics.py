"""Exact tests for the determinant geometry, the prime cutoff and the angular budget."""
import argparse
import hashlib
import json
import sys
from fractions import Fraction as F
from itertools import combinations
from math import ceil, floor
from pathlib import Path
from zipfile import ZipFile

HERE = Path(__file__).resolve().parent
BASE = HERE / "base-checkpoint.zip"
DIGEST = "2ce6b595f27c88909a91e529fc4a426270e2a061e620072c925deb1a3c82e487"
assert hashlib.sha256(BASE.read_bytes()).hexdigest() == DIGEST
sys.path.insert(0, str(BASE))
from poisson_fourier import integrals, pi_interval, log_interval


def enclosure(lo, hi=None, digits=12):
    scale = 10**digits
    return [floor(lo*scale), ceil((lo if hi is None else hi)*scale)]


def geometry(widths, ratios):
    u = [F(w, 10000) for w in widths]
    v = len(ratios)-1
    length = 2*sum(u)
    rows = [length*r/(2*sum(ratios)-ratios[0]) for r in ratios[:0:-1]+ratios]
    groups = [sorted((r for i,r in enumerate(rows) if (i-v)%4 == l), reverse=True) for l in range(4)]
    row_terms = [(width,j) for group in groups for j,width in enumerate(group)]
    col_terms = [(width/2,j) for j,width in enumerate(u) for l in range(4)]
    gap = [sum(sum(group[:j+1]) for group in groups)-2*sum(u[:j+1]) for j in range(len(u))]
    assert gap[-1] == 0 and min(gap) >= 0
    return length, row_terms, col_terms, gap


def cutoff_proof(rows, cols, top=F(1,24)):
    # For h<T, go through every kink of a function of one variable.
    # For h>=T, also allow x=h*y to vary continuously above T*y.
    T = max(j for _,j in rows+cols)
    terms = [(w,j,1) for w,j in rows]+[(w,j,-1) for w,j in cols]
    low_count = 0
    for h in range(1,T):
        knots = {F(0), top}
        for width,j,_ in terms:
            if h>j and width/(h-j)<top:
                knots.add(width/(h-j))
        for y in knots:
            diff = sum(sign*max(0,width-max(0,h-j)*y) for width,j,sign in terms)
            assert diff >= 0, ("low",h,y,diff)
        low_count += len(knots)

    # Every linear piece of R-C achieves a minimum at a vertex in this polygon.
    ceiling = max(w+j*top for w,j,_ in terms)
    lines = {(w,j) for w,j,_ in terms} | {(F(0),T),(ceiling,0)}
    vertices = {(y,c+m*y) for y in (F(0),top) for c,m in lines if T*y<=c+m*y<=ceiling}
    for (c,m),(b,n) in combinations(lines,2):
        if m != n:
            y = (b-c)/(m-n)
            x = c+m*y
            if 0<=y<=top and T*y<=x<=ceiling:
                vertices.add((y,x))
    for y,x in vertices:
        val = sum(sign*max(0,w+j*y-x) for w,j,sign in terms)
        assert val >= 0, ("polygon",y,x,val)
    return dict(small_height_points=low_count,polygon_vertices=len(vertices),all_cutoff_gains="0")


def angle_test(z,table,fields):
    dim = len(next(iter(fields.values())))-1
    low = [F(0)]*dim
    high = [F(0)]*dim
    start = 0
    for l,r,mix in table["allocation"]:
        assert l == start < r and sum(n for _,n in mix)==table["unit"]
        start = r
        a,b = integrals(z,F(l,table["grid"]))[1],integrals(z,F(r,table["grid"]))[1]
        p,q = b[0]-a[1],b[1]-a[0]
        for name,n in mix:
            k = fields[name]
            for i in range(dim):
                weight = F(n*(k[i+1]-k[i]), table["unit"]*100000)
                v,w = weight*p,weight*q
                low[i] += min(v,w)
                high[i] += max(v,w)
    assert start == table["grid"]
    pi_lo,pi_hi = pi_interval()
    factor = (1/z-z)/4
    lower = [factor*pi_lo-x for x in high]
    upper = [factor*pi_hi-x for x in low]
    return enclosure(min(lower),min(upper)), 1+upper.index(min(upper))


def run():
    def data(name):
        return json.loads(archive.read(name))
    out = []
    with ZipFile(BASE) as archive:
        cases = data("certificate.json")["cases"]
        for report in cases:
            d = report["d"]
            old = data(f"prior/reference/baseline/case{d}.json")
            current = data(f"balanced{d}.json")
            assert current["even"]==current["odd"]
            for name,u,r,z,tab,fields in (
                ("section8",old["shape"]["u"],old["shape"]["a"],F(old["z"]),old,
                 {t["label"]:t["field"] for t in old["witness"]["knots"]}),
                ("current",current["even"],current["a"],F(current["z"]),data(f"angles{d}.json"),
                 {tag:t["field"] for tag,t in data(f"final-fields{d}.json")["ordinary"].items()})):
                length,rows,cols,gaps = geometry(u,r)
                row_list = sorted((w for w,_ in rows),reverse=True)
                band_list = sorted((F(2*w,10000) for w in u),reverse=True)
                diffs = [sum(row_list[:s])-sum(band_list[:s]) for s in range(1,len(band_list)+1)]
                assert all(x>=0 for x in diffs) and diffs[-1]==0 and len(row_list)<=len(band_list)
                row = dict(d=d,shape=name,L=str(length),min_prefix=str(min(gaps[:-1])),last=str(gaps[-1]),
                           prefix_by_J=[str(x) for x in gaps],
                           full_step_majorization=[str(x) for x in diffs],cutoffs=cutoff_proof(rows,cols))
                shifts = ("0","0.000001","0.0001","0.001")
                row["direction_slacks"]={delta:angle_test(z+F(delta),tab,fields) for delta in shifts}
                if name=="current":
                    constants = report["balanced"]["constants"]
                    D,K,A,price = (F(constants[k]) for k in ("D","K","A","Lambda"))
                    C = F(current["C"])
                    b=F(current["b"])
                    tightened={2:F("16.161227"),3:F("27.412216")}[d]+1
                    step0=C-tightened
                    B=b*K
                    direct=B-(2*B-tightened-b*price)**2/(8*B)-D-b*A
                    assert 0<step0 and 3*(tightened-d+1)+b*price>2*B>tightened+b*price and direct>0
                    prior=data("independent.json")["cases"][d-2]["balanced"]
                    low,high=log_interval(1/z)
                    b0,b1=b*length*low/2,b*length*high/2
                    assert b0>1 and tightened>6*b1/5 and 3*(tightened-d+1)>2*b1
                    main_lower=F(prior["margin_lower"])-step0/5
                    secondary_lower=F(prior["secondary_minus_loss_lower"])-step0/(4*b0)
                    assert main_lower>0 and secondary_lower>0
                    row["uniform_endpoint"]={"w":str(tightened-1),"b":str(b),"direct_margin":enclosure(direct),
                        "independent_main_margin_at_least":str(main_lower),
                        "independent_secondary_margin_at_least":str(secondary_lower)}
                    log2lo,log2hi = log_interval(2)
                    costs = {}
                    for step in (1,2):
                        t = D/(C-step)
                        assert 0<t<1
                        cost = (A-K*((1-t)**2+t*t)-price*t)/d
                        costs[str(step)]={"G":enclosure(cost),"ramified_valuation":enclosure(2*cost/log2hi,2*cost/log2lo)}
                    row["required_saving_at_any_b"]=costs
                    row["stored_threshold_interval"]=constants["threshold"]
                    nnode=len(rows)
                    jcount=len(u)
                    quotient,remainder=divmod(-2*jcount,nnode)
                    phi=nnode*quotient*(quotient-1)//2+remainder*quotient
                    tail=F(phi,2*280**2)/length
                    # Even granting the entire tail at its upper bound, this target fails the trial.
                    trial_reduction={2:F(25,100000),3:F(32,100000)}[d]
                    p=D/(C-trial_reduction)
                    required=(A-K*((1-p)**2+p*p)-price*p)/d
                    assert tail<required
                    row["unscanned_window_tail"]={"upper":str(tail),"interval":enclosure(tail),
                        "impossible_reduction_with_tail_alone":str(trial_reduction)}
                out.append(row)
    return dict(interval_scale=10**12,cases=out)


if __name__=="__main__":
    if not __debug__:
        raise RuntimeError("Enable assertions")
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json",type=Path)
    args=parser.parse_args()
    report=run()
    if args.json:
        args.json.write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8")
    for case in report["cases"]:
        print(case["shape"],case["d"],case["cutoffs"],case["direction_slacks"],case.get("required_saving_at_any_b",""))

