"""Independent cutoff proof by ordered partial sums, and exact rational Cauchy-pencil verification."""
import argparse
import hashlib
import json
import sys
from fractions import Fraction as F
from itertools import combinations
from math import ceil, floor, gcd, isqrt, prod
from functools import reduce
from pathlib import Path
from zipfile import ZipFile

HERE=Path(__file__).resolve().parent
BASE=HERE/"base-checkpoint.zip"
assert hashlib.sha256(BASE.read_bytes()).hexdigest()=="2ce6b595f27c88909a91e529fc4a426270e2a061e620072c925deb1a3c82e487"
sys.path.insert(0,str(BASE))
from poisson_fourier import log_interval


def cap_check(widths,ratios):
    L=F(sum(widths),5000)
    T=len(widths)-1
    a=[(L*v/(2*sum(ratios)-ratios[0]),i-len(ratios)+1) for i,v in enumerate(ratios[:0:-1]+ratios)]
    r=[(v,j) for l in range(4) for j,(v,_) in enumerate(sorted(((v,i) for v,i in a if i%4==l),reverse=True))]
    c=[(F(v,20000),j) for j,v in enumerate(widths)]*4
    # Sum of the largest s of the clipped widths is affine until an order switch or a zero.
    top=F(1,24)
    points={F(0),top}
    for side in (r,c):
        for (a,i),(b,j) in combinations(side+[(F(0),T)],2):
            if i!=j:
                y=(b-a)/(i-j)
                if 0<y<top:points.add(y)
    for y in points:
        aa=sorted((max(0,a-(T-i)*y) for a,i in r),reverse=True)
        bb=sorted((max(0,b-(T-j)*y) for b,j in c),reverse=True)
        for s in range(1,max(len(aa),len(bb))+1):
            assert sum(aa[:s])>=sum(bb[:s])
    for h in range(1,T):
        cuts=sorted({F(0),top,*(w/(h-g) for w,g in r+c if g<h and w/(h-g)<top)})
        for left,right in zip(cuts,cuts[1:]):
            mid=(left+right)/2
            active=[(w,max(0,h-g),sgn) for src,sgn in ((r,1),(c,-1)) for w,g in src if w>max(0,h-g)*mid]
            const=sum(w*sgn for w,k,sgn in active);slope=-sum(k*sgn for w,k,sgn in active)
            assert const+min(slope*left,slope*right)>=0
    return len(points)


def determinant(A):
    A=[row[:] for row in A]
    ans=1
    for i in range(len(A)):
        j=next((j for j in range(i,len(A)) if A[j][i]),None)
        if j is None:return F(0)
        if j!=i:
            A[i],A[j]=A[j],A[i];ans=-ans
        pivot=A[i][i];ans*=pivot
        for j in range(i+1,len(A)):
            mul=A[j][i]/pivot
            if mul:
                for t in range(i+1,len(A)):
                    A[j][t]-=mul*A[i][t]
    return ans


def check_pencil(c,progressions,k,factor):
    m=c["m"];p=list(map(int,c["primitive_coefficients"]))
    assert len(p)==m+1 and p[-1]>0 and reduce(gcd,p)==1
    x=list(range(0,2*m,2));y=list(range(1,2*m,2))
    cauchy=F((-1)**(m*(m-1)//2)*prod(b-a for a,b in combinations(x,2))*prod(b-a for a,b in combinations(y,2)),
             prod(i-j for i in x for j in y))
    leading=cauchy*(-2/factor)**m
    s=[sum((F((-1)**j,(a*j+b)**k) for a,b in progressions for j in range(i)),F(0)) for i in range(2*m)]
    for t in range(2*m,3*m+1):
        A=[[(s[i]+s[j]-2*F(t)/factor)/(i-j) for j in y] for i in x]
        assert p[-1]*determinant(A)==leading*sum(v*t**j for j,v in enumerate(p))


def main():
    with ZipFile(BASE) as archive:
        points=[]
        for d in (2,3):
            old=json.loads(archive.read(f"prior/reference/baseline/case{d}.json"))["shape"]
            new=json.loads(archive.read(f"balanced{d}.json"))
            points.extend([cap_check(old["u"],old["a"]),cap_check(new["even"],new["a"])])
    # Target normalizations are specified here independently of the producer.
    cases={"pi^2":([(1,1)],2,F(12)),"pi^3":([(2,1)],3,F(32)),
           "Catalan":([(2,1)],2,F(1)),"zeta(3)":([(1,1)],3,F(4,3)),
           "pi^4":([(1,1)],4,F(720,7)),"L(2,chi_-3)":([(3,1),(3,2)],2,F(2,3)),
           "log(2)":([(1,1)],1,F(1)),"pi":([(2,1)],1,F(4))}
    primitive=json.loads((HERE/"constants.json").read_text())
    assert {(row["target"],row["m"]) for row in primitive["cases"]}=={(n,m) for n in cases for m in (4,8,12,16)}
    for c in primitive["cases"]:check_pencil(c,*cases[c["target"]])
    n=10**20;s=isqrt(2*n*n)
    assert s*s<2*n*n<(s+1)**2
    ell_lo=log_interval(3+2*F(s,n))[0]
    ell_hi=log_interval(3+2*F(s+1,n))[1]
    lo,hi=log_interval(F(2));rates={}
    for v in (1,2,3,4):
        a=lo+F(1,6)+ell_lo/(2*v);b=hi+F(1,6)+ell_hi/(2*v)
        rates[str(v)]=[floor(a*10**12),ceil(b*10**12)]
    return dict(status="passed",cutoff_sort_break_counts=points,
                independent_primitive_polynomial_checks=len(primitive["cases"]),rate_scale=10**12,decay_rates=rates)


if __name__=="__main__":
    if not __debug__:
        raise RuntimeError("Enable assertions")
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json",type=Path)
    args=parser.parse_args();out=main()
    if args.json:args.json.write_text(json.dumps(out,indent=2)+"\n",encoding="utf-8")
    print(out)

