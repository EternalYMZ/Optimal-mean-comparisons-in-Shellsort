"""Full finite mean for the predetermined powers of two below n, with integer enclosures."""
from fractions import Fraction as F
from functools import cache
from math import comb,isqrt
from pathlib import Path

UNIT=10**24


def out(x,upper):
    q,r=divmod(x.numerator*UNIT,x.denominator)
    return F(q+int(upper and r>0),UNIT)


def atan_inv(q):
    s=sum((F((-1)**j,(2*j+1)*q**(2*j+1)) for j in range(41)),F())
    return s-F(1,83*q**83),s


alo,ahi=atan_inv(5)
blo,bhi=atan_inv(239)
PI_LO,PI_HI=16*alo-4*bhi,16*ahi-4*blo


def sqrt_out(x,upper):
    q=isqrt((UNIT**2*x.numerator)//x.denominator)
    return F(q+int(upper and q*q*x.denominator<UNIT**2*x.numerator),UNIT)


@cache
def cross(m):
    if m==0:
        return F(0),F(0)
    if m<=65536:
        a=F(m*(4**(m-1)),comb(2*m,m))
        return out(a,False),out(a,True)
    a=F(m)+F(1,4)
    b=a+F(1,32*m)
    return F(m,4)*sqrt_out(PI_LO*a,False),F(m,4)*sqrt_out(PI_HI*b,True)


def chain(length):
    m,r=divmod(length,2)
    lo,hi=cross(m)
    if r:
        factor=F(2*(m+1),2*m+1)
        lo*=factor
        hi*=factor
    records=1+F(m,length)
    return lo+length-records,hi+length-records


def fixed_mean(n):
    if n<2:
        return []
    h=1<<((n-1).bit_length()-1)
    rows=[(h,F(n-h),F(n-h))]
    while h>1:
        h//=2
        m,r=divmod(n,h)
        lo,hi=chain(m)
        plo,phi=chain(m+1)
        rows.append((h,(h-r)*lo+r*plo,(h-r)*hi+r*phi))
    return rows


if __name__=="__main__":
    from verify_race import exhaustive
    for n in range(2,10):
        rows=fixed_mean(n)
        direct=exhaustive(n,[h for h,_,_ in rows])
        assert all(lo<=c<=hi for (_,lo,hi),(_,c) in zip(rows,direct))
    n=10**9
    rows=fixed_mean(n)
    lo=sum(x for _,x,_ in rows)
    hi=sum(x for _,_,x in rows)
    print("n",n,"passes",len(rows),"integer outer bounds",lo//1,-(-hi//1))
    print("interval endpoints in millionths (outward)",(lo*10**6)//1,-(-(hi*10**6)//1))
    print("all passes checked at n=2..9")
