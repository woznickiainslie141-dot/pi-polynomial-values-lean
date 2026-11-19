"""Exact primitive determinant polynomials and two enclosures of their values.
Python 3.10+ standard library. The natural target is Y = factor * alternating sum.
"""
import argparse
import json
from fractions import Fraction as F
from functools import reduce
from math import factorial, gcd, lcm
from pathlib import Path

# Positive moment sums with the same power k in each progression.
CASES = {
    "pi^2": ([(1,1)],2,F(12)), "pi^3": ([(2,1)],3,F(32)),
    "Catalan": ([(2,1)],2,F(1)), "zeta(3)": ([(1,1)],3,F(4,3)),
    "pi^4": ([(1,1)],4,F(720,7)), "L(2,chi_-3)": ([(3,1),(3,2)],2,F(2,3)),
    "log(2)": ([(1,1)],1,F(1)), "pi": ([(2,1)],1,F(4))
}


def moment(h, data, k):
    return sum((F(1,(a*h+b)**k) for a,b in data), F(0))


def target_interval(data,k,factor,bits,base):
    # 1/(1+x)=(base-1)/base * sum ((1-(base-1)*x)/base)^r.
    B = 1<<bits
    count = bits+4 if base==2 else (bits*2)//3+5
    assert base**count >= B and base in (2,3)
    queue = [(q.numerator*B)//q.denominator for q in (moment(j,data,k) for j in range(count))]
    total,den = 0,base
    for r in range(count):
        total += (base-1)*queue[0]//den
        queue = [a-(base-1)*b for a,b in zip(queue,queue[1:])]
        den *= base
    # At stage r, sum of absolute coefficients is base^r. The geometric tail is at most c0/base^count.
    radius=2*count+len(data)+1
    lo=F(total-radius)*factor
    hi=F(total+radius)*factor
    return lo.numerator//lo.denominator,-((-hi.numerator)//hi.denominator)


def bareiss(matrix):
    A = [r[:] for r in matrix]
    sign,last = 1,1
    for k in range(len(A)-1):
        pivot = next((i for i in range(k,len(A)) if A[i][k]),None)
        if pivot is None:
            return 0
        if pivot!=k:
            A[k],A[pivot] = A[pivot],A[k]
            sign=-sign
        v=A[k][k]
        for i in range(k+1,len(A)):
            for j in range(k+1,len(A)):
                q,r=divmod(A[i][j]*v-A[i][k]*A[k][j],last)
                assert r==0
                A[i][j]=q
        last=v
    return sign*A[-1][-1]


def matrix_pencil(m,data,k,factor):
    even=[2*i for i in range(m)]
    odd=[2*i+1 for i in range(m)]
    s=[F(0)]
    for h in range(odd[-1]):
        s.append(s[-1]+(-1)**h*moment(h,data,k))
    a,b=[],[]
    for h in even:
        v=[(s[h]+s[t])/(h-t) for t in odd]
        w=[-F(2)/(factor*(h-t)) for t in odd]
        den=lcm(*(i.denominator for i in v+w))
        a.append([int(i*den) for i in v])
        b.append([int(i*den) for i in w])
    return a,b


def integer_value(A,B,t):
    return bareiss([[u+t*v for u,v in zip(a,b)] for a,b in zip(A,B)])


def polynomial(m,A,B):
    values=[integer_value(A,B,t) for t in range(m+1)]
    p=[0]*(m+1)
    falling=[1]
    for j in range(m+1):
        v=values[0]*factorial(m)//factorial(j)
        for i,x in enumerate(falling):
            p[i]+=x*v
        falling=[a-j*b for a,b in zip([0]+falling,falling+[0])]
        values=[b-a for a,b in zip(values,values[1:])]
    divisor=reduce(gcd,p)
    assert divisor and p[-1]
    return [c//(divisor if p[-1]>0 else -divisor) for c in p]


def exact_horner(p,t):
    value=0
    for c in reversed(p):
        value=value*t+c
    return value


def image_interval(p,target,bits):
    den=1<<bits
    l,h=target
    v,w=0,0
    for c in reversed(p):
        vals=(v*l,v*h,w*l,w*h)
        v=c*den+min(vals)//den
        w=c*den-((-max(vals))//den)
    assert w<0 or v>0, "Increase target precision to decide the sign"
    return (v,w) if v>0 else (-w,-v)


def experiment():
    records=[]
    for name,(data,k,factor) in CASES.items():
        # Each enclosure is computed independently from raw rational moments.
        bits=1344
        targets=[target_interval(data,k,factor,bits,base) for base in (2,3)]
        assert max(t[0] for t in targets)<=min(t[1] for t in targets)
        for m in (4,8,12,16):
            A,B=matrix_pencil(m,data,k,factor)
            p=polynomial(m,A,B)
            # m+1 additional integer points certify equality up to a *single* rational multiplier.
            v=bareiss(B)
            assert v and reduce(gcd,p)==1 and p[-1]>0
            for t in range(-1,-m-2,-1):
                assert integer_value(A,B,t)*p[-1] == v*exact_horner(p,t)
            bounds=[image_interval(p,t,bits) for t in targets]
            small=min(t[0] for t in bounds)
            large=max(t[1] for t in bounds)
            e=small.bit_length()-1-bits
            assert large.bit_length()-1-bits == e
            records.append(dict(target=name,m=m,primitive_coefficients=list(map(str,p)),
                                height_bits=max(abs(c).bit_length() for c in p),
                                log2_abs_floor=e))
    return dict(status="passed",cases=records)


if __name__=="__main__":
    if not __debug__:
        raise RuntimeError("Enable assertions")
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json",type=Path)
    args=parser.parse_args()
    report=experiment()
    if args.json:
        args.json.write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8")
    for c in report["cases"]:
        print(c["target"],c["m"],c["height_bits"],c["log2_abs_floor"])

