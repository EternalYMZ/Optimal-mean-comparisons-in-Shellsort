"""Exact-rank and rational checks for the finite hidden-interior obstruction."""
from fractions import Fraction as F
from itertools import combinations, permutations
from math import comb, factorial
from pathlib import Path
import sys

work_path=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(work_path/"billion_joint_2026-11-22"/"divisors"))
from check import LN2, cross, log_bounds, sqrt_out


def interior_bound(n,m,d):
    """Known balanced occupancy counts of a consecutive m-slot interval mod d."""
    l,s=divmod(m,d)
    return F(n+1,2)*sum(count*cross(min(u,m-u))[0]/(2*min(u,m-u)+1)
                        for u,count in ((l,d-s),(l+1,s)) if count)


def entropy_parameters(n,D):
    Q=max(2,1+(2*D)//n)
    a=min(n,2*Q-1)
    entropy=log_bounds(F(n,a))[0]-(1+log_bounds(a)[1])/a-2*D/(n*(Q-1))
    # Use the directed endpoint according to the sign of the numerator.
    bits=entropy/LN2[int(entropy>=0)]
    return Q,bits


def comparison_threshold(n,D):
    Q,bits=entropy_parameters(n,D)
    cap1=(D-n+1)//(50*n-n*bits-n+1)
    cap2=F(Q-1,2)*LN2[0]
    cap=min(cap1, -(-cap2//1)-1)
    assert cap>0 and 2*F(cap,Q-1)<LN2[0]
    lower=n*bits+n-1+(D-n+1)/cap
    assert lower>=50*n
    return int(cap),lower//1


def necessary_cross_moves(n,D,H,d):
    remaining_obligation=F(D-50*n*H,n+1)
    return max(0, F(4,d)*max(0,remaining_obligation)**2)


def resonant_result(n,m,d,amount):
    assert d%2==0 and m%d==0
    D0=F(n+1,m+1)*cross(m//2)[0]
    # A putative passing table gives at most 50 n total moves, so all mid
    # gaps having circle-step <=amount give weighted budget <=50 n amount/d.
    Deff=D0-(n+1)*sqrt_out(F(50*n*amount,d),True)
    return comparison_threshold(n,Deff)


def conditional_bound(n,m,d,amount,H,cap):
    D0=F(n+1,m+1)*cross(m//2)[0]
    paid=F(cap)
    D=F(0)
    for _ in range(10):
        D=max(D,D0-(n+1)*sqrt_out(F(amount,d)*paid,True))
        residual=max(n-1,n-1+(D-n+1)/H)
        # If the whole mean is < cap, the average comparisons in the
        # middle cannot exceed the budget after the suffix.
        paid=max(0,cap-residual)
    Q,bits=entropy_parameters(n,D)
    assert 2*F(H,Q-1)<LN2[0]
    return n*bits + n-1 + (D-n+1)/H


def cuts_footrule(a):
    return sum(abs(i-x) for i,x in enumerate(a))


def run(a,word):
    a=list(a)
    for h in word:
        for r in range(h):
            a[r::h]=sorted(a[r::h])
    return a


def swaps(a,h):
    return sum(a[i]>a[j] for j in range(h,len(a)) for i in range(j-h,-1,-h))


def median_deviations(m,u,t):
    cnt=[]
    for x in range(max(0,u+t-m),min(u,t)+1):
        weight=comb(u,x)*comb(m-u,t-x)
        cnt.append((x,weight))
    den=comb(m,t)
    return F(min(sum(abs(y-x)*a for y,a in cnt) for x,a in cnt),den)


def verify():
    comparisons=0
    for m in range(2,38):
        for u in range(1,m):
            v=min(u,m-u)
            lo=cross(v)[0]
            exact=sum(median_deviations(m,u,t) for t in range(m+1))
            assert exact>=(m+1)*lo/(2*v+1)
            if 2*u==m:
                assert exact==F(u*4**(u-1),comb(2*u,u))
            comparisons+=1
    checks=0
    words=0
    for n in range(3,8):
        for r in range(0,(n-2)//2+1):
            Htop=n-r
            for d in range(2,min(n,5)):
                m=n-2*r
                l,s=divmod(m,d)
                exact=F(n+1,2*(m+1))*sum(c*sum(median_deviations(m,u,t) for t in range(m+1))
                                         for u,c in ((l,d-s),(l+1,s)) if c)
                lower=interior_bound(n,m,d)
                assert exact>=lower
                for upper in ((),tuple(range(n-1,Htop-1,-1))):
                    mid=tuple(h for h in range(Htop-1,0,-1) if h%d==0)
                    traces=[run(a,upper+mid) for a in permutations(range(n))]
                    ef=F(sum(cuts_footrule(a) for a in traces),2*factorial(n))
                    assert ef>=exact>=lower,(n,r,d,upper,mid,ef,lower)
                    checks+=len(traces)
                    words+=1
    print("hypergeometric median checks",comparisons)
    print("head/middle combinations",words,"permutation runs",checks)

    checks=0
    for n in range(4,8):
        for r in range((n-2)//2+1):
            m=n-2*r
            top=tuple(range(n-1,n-r-1,-1))
            for d in range(2,min(n,5)):
                base=interior_bound(n,m,d)
                arc=F(n+1,m+1)*cross(m//2)[0] if d%2==0 and m%d==0 else None
                if arc is not None:
                    assert arc>=0
                for count in range(1,min(3,n-r)):
                    for chosen in combinations(range(1,n-r),count):
                        middle=chosen[::-1]
                        paid=arc_paid=dist=0
                        for a in permutations(range(n)):
                            a=run(a,top)
                            for h in middle:
                                rem=h%d
                                if rem:
                                    paid+=swaps(a,h)
                                    arc_paid+=min(rem,d-rem)*swaps(a,h)
                                a=run(a,(h,))
                            dist+=cuts_footrule(a)
                        D=F(dist,2*factorial(n))
                        assert max(0,base-D)**2<=F((n+1)**2*d*paid,4*factorial(n))
                        if arc is not None:
                            assert max(0,arc-D)**2<=F((n+1)**2*arc_paid,d*factorial(n))
                        checks+=1
    print("mixed-residue mean checks",checks)


if __name__=="__main__":
    n=10**9
    print("untouched_count_before_middle,modulus,D_floor,H_largest_excluded,mu_floor")
    for r in (n//10,n//4,3*n//8):
        for d in (2,3,5,10,100,1000,10**6):
            D=interior_bound(n,n-2*r,d)
            H,lower=comparison_threshold(n,D)
            print(n-2*r,d,D//1,H,lower,sep=",")
    m=n//2
    for H in (1,16,50,70):
        R=necessary_cross_moves(n,interior_bound(n,m,2),H,2)
        print("parity midpoint cross moves under 50b hypothesis",H,R//1)
    for d,amount in ((10**5,1),(10**6,1),(10**6,2),(10**6,10),(10**7,10)):
        H,lower=resonant_result(n,m,d,amount)
        print("near residue obstruction",d,amount,H,lower)
        cap=50*n
        good=[h for h in range(H,103) if conditional_bound(n,m,d,amount,h,cap)>=cap]
        h=max(good)
        # Fixed independent comparison levels give unconditional lower bounds
        # by contradiction under the hypothesis that the actual mean is smaller.
        best=max(a for a in range(cap,cap+n,10**7) if conditional_bound(n,m,d,amount,h,a)>=a)
        print("near residue obstruction after reserving suffix comparisons",d,amount,h,best)
    verify()
