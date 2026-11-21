"""Theory-only finite table bounds, using directed rational logarithms."""
from fractions import Fraction as Q
from functools import cache
from math import factorial
from pair import smooth
from final_pass import holes

SCALE=10**18

def unitlog(x):
    # 1<=x<=2; ln x = 2 sum y^(2j+1)/(2j+1).
    y=(x-1)/(x+1)
    term=y
    s=Q(0)
    for j in range(24):
        s+=2*term/(2*j+1)
        term*=y*y
    return s,s+2*term/(49*(1-y*y))

@cache
def logs(x):
    x=Q(x)
    k=x.numerator.bit_length()-x.denominator.bit_length()
    u=x/(Q(2)**k)
    if u<1:
        u*=2; k-=1
    assert 1<=u<2
    l,h=unitlog(u); a,b=unitlog(Q(2))
    l+=k*(a if k>=0 else b)
    h+=k*(b if k>=0 else a)
    return Q((l*SCALE)//1,SCALE),Q(-(-(h*SCALE)//1),SCALE)

def first(n,h):
    l,r=divmod(n,h)
    support=Q(0); cost=Q(0)
    for length,count in ((l,h-r),(l+1,r)):
        support+=count*logs(factorial(length))[1]
        cost+=count*sum(Q(q,2)+Q(q,q+1) for q in range(1,length))
    return cost,support

def lower(n,word,t,price_first=True):
    entropy=n*(logs(n)[0]-1)
    cost=0
    if price_first:
        cost,info=first(n,word[0])
        entropy-=info
        word=word[1:]
    visits=sum(n-h for h in word)
    # G_q(t)=[1+(1-2t)t^(q-1)]/(1-t). Bound the tail q>17.
    lz=visits*logs(1/(1-t))[1]
    remaining=visits
    for q in range(1,18):
        count=sum(min(h,max(0,n-q*h)) for h in word)
        lz+=count*logs(1+(1-2*t)*t**(q-1))[1]
        remaining-=count
    lz+=remaining*(1-2*t)*t**17
    net=entropy-lz
    denominator=logs(1/t)[1 if net>=0 else 0]
    return cost+visits+net/denominator

def show():
    n=10**9
    for ab in [(3,5),(7,13),(9,10),(4,45),(5,27),(9,11),(8,13),(10,11),(7,18),(8,15),(11,12),(11,13)]:
        word=smooth(n,ab)
        ts=[Q(1,k) for k in range(6,12)]
        full,t=max((lower(n,word,t),t) for t in ts)
        generic=max(lower(n,word,t,False) for t in ts)
        scans=sum(n-h for h in word)
        missing=holes(ab)
        def local(m):
            # Each key touches at most the number of possible missing distances.
            return m*sum(g<m for g in missing)//2 + m-1
        upper=0
        for h in word:
            l,r=divmod(n,h)
            upper+=(h-r)*local(l)+r*local(l+1)
        top,_=first(n,word[0])
        l,r=divmod(n,word[0])
        upper+=top-(word[0]-r)*local(l)-r*local(l+1)
        print(ab,len(word),scans,generic//1,full//1,t,-(-upper//1))

if __name__=='__main__':
    show()
