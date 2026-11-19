"""Finite tests of Gaussian common content on prefix determinants, with two valuation algorithms."""
import argparse
import json
from math import comb, factorial
from pathlib import Path
from zipfile import ZipFile

BASE=Path(__file__).resolve().parent/"base-checkpoint.zip"


def valuation_two(x):
    return (x&-x).bit_length()-1


def matrix(case,N,tau):
    u=case["even"]
    assert u==case["odd"]
    cuts=[w*N//10000 for w in u]
    columns=[(t,j) for j,c in enumerate(cuts) for t in range(-c,c+1)]
    n=len(columns)
    ratios=case["a"]
    rr=ratios[:0:-1]+ratios
    den=sum(rr)
    heights=[n*w//den for w in rr]
    order=sorted(range(len(rr)),key=lambda i:(-(n*rr[i]%den),(i-len(rr)//2)**2,i))
    for i in order[:n-sum(heights)]:
        heights[i]+=1
    assert sum(heights)==n
    max_order=len(u)-1
    coeff={}
    for t in range(-cuts[0],cuts[0]+1):
        p=[1]+[0]*max_order
        for s in range(max(heights)):
            coeff[t,s]=p
            p=[(t-s)*a+b for a,b in zip(p,[0]+p[:-1])]
    M=[]
    paid=0
    for i,height in enumerate(heights):
        v=i-len(rr)//2
        for s in range(height):
            paid+=s-s.bit_count()
            row=[]
            for t,j in columns:
                q=sum(comb(j,r)*2**r*(v*tau)**(j-r)*factorial(r)*coeff[t,s][r] for r in range(min(j,s)+1))
                row.append(((q,0),(0,q),(-q,0),(0,-q))[(v*t)%4])
            M.append(row)
    return M,2*paid,heights


def norm_valuation(matrix,bits):
    # v_2(det [[Re,-Im],[Im,Re]]) is v_{1+i} of the Gaussian determinant.
    A=[[z[0] for z in row]+[-z[1] for z in row] for row in matrix]
    A += [[z[1] for z in row]+[z[0] for z in row] for row in matrix]
    mod=1<<bits
    val=0
    while A:
        n=len(A)
        pivot=next(((i,j) for i,row in enumerate(A) for j,v in enumerate(row) if v&1),None)
        if pivot is None:
            if mod<=2 or not any(x%mod for row in A for x in row):
                return None
            A=[[x//2 for x in row] for row in A]
            mod//=2
            val+=n
            continue
        i,j=pivot
        A[0],A[i]=A[i],A[0]
        for row in A:
            row[0],row[j]=row[j],row[0]
        first=A[0][1:]
        inv=pow(A[0][0],-1,mod)
        new=[]
        for row in A[1:]:
            fac=(row[0]*inv)%mod
            new.append([(a-fac*b)%mod for a,b in zip(row[1:],first)] if fac else row[1:])
        A=new
    return val


def gaussian_valuation(matrix,bits):
    A=[row[:] for row in matrix]
    mod=1<<bits
    val=0
    while A:
        n=len(A)
        pivot=next(((i,j) for i,row in enumerate(A) for j,(a,b) in enumerate(row) if (a-b)&1),None)
        if pivot is None:
            if mod<=2 or not any(a%mod or b%mod for row in A for a,b in row):
                return None
            A=[[((a+b)//2,(b-a)//2) for a,b in row] for row in A]
            mod//=2
            val+=n
            continue
        i,j=pivot
        A[0],A[i]=A[i],A[0]
        for row in A:
            row[0],row[j]=row[j],row[0]
        first=A[0][1:]
        a,b=A[0][0]
        inv=pow(a*a+b*b,-1,mod)
        new=[]
        for row in A[1:]:
            c,d=row[0]
            s=(inv*(a*c+b*d))%mod
            t=(inv*(a*d-b*c))%mod
            new.append([((x-s*u+t*v)%mod,(y-s*v-t*u)%mod)
                        for (x,y),(u,v) in zip(row[1:],first)] if (s or t) else row[1:])
        A=new
    return val


def verify():
    result=[]
    with ZipFile(BASE) as archive:
        for d in (2,3):
            case=json.loads(archive.read(f"balanced{d}.json"))
            for N in (2,4,6,8):
                M,paid,heights=matrix(case,N,1)
                # Y=-i. Gaussian elimination and the norm over Z perform different reductions.
                norm=norm_valuation(M,256)
                gauss=gaussian_valuation(M,256)
                assert norm is not None and gauss==norm,(d,N,norm,gauss)
                result.append(dict(d=d,N=N,n=len(M),row_heights=heights,norm_valuation=norm,
                                   ramified_valuation=norm-paid,denominator_adjustment=paid))
    return result


if __name__=="__main__":
    if not __debug__:
        raise RuntimeError("Enable assertions")
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json",type=Path)
    args=parser.parse_args()
    out=verify()
    if args.json:
        args.json.write_text(json.dumps(out,indent=2)+"\n",encoding="utf-8")
    for row in out:
        print(row["d"],row["N"],row["n"],row["ramified_valuation"])

