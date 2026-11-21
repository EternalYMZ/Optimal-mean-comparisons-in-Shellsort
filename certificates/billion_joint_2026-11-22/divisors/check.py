"""Deterministic certificates for the checkpoint at the first gap not divisible by d."""
from fractions import Fraction as F
from functools import cache
from itertools import combinations, permutations
from math import comb,isqrt
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "fixed_word_mean_2026-11-22"))
from dyadic import cross, PI_LO, PI_HI, sqrt_out


def exact_bridge(m):
    return F(m * 4**(m-1), comb(2*m, m))


def payoff(n,d):
    size, long_count = divmod(n, d)
    assert 2*(size+int(bool(long_count))) <= n
    return F(n+1,2) * sum(mult * cross(l)[0]/(2*l+1)
                            for mult, l in ((d-long_count,size),(long_count,size+1))
                            if mult)


def ln_core(x):
    assert 1 <= x <= 2
    v = (x-1)/(x+1)
    s = sum(2*v**(2*j+1)/(2*j+1) for j in range(21))
    return s, s + 2*v**43/(43*(1-v*v))


LN2 = ln_core(F(2))


@cache
def log_bounds(x):
    x = F(x)
    assert x >= 1
    k = x.numerator.bit_length() - x.denominator.bit_length()
    if x < 2**k:
        k -= 1
    lo,hi = ln_core(x/2**k)
    return lo+k*LN2[0], hi+k*LN2[1]


def cut_bound(n,d):
    m,r=divmod(n,d)
    N = m*d
    if m < 16:
        return F(0)
    c = isqrt(m)
    delta = F(1,12)*(F(d,d-1)*F(2,c)+F(1,N))
    integral = PI_LO*m*m/8 - F(m,2) - 2*c*sqrt_out(F(c*m),True)
    factor = sqrt_out(F(d*(d-1),2*m)/PI_HI,False)
    if integral < 0 or delta>=1:
        return F(0)
    return d*(1-delta)*factor*integral-F(N*(d-1),2)-r*n


def stein_interval(n,d):
    m,rem=divmod(n,d)
    lo = hi = F(0)
    for count,l,r0 in ((rem,m+1,0),(d-rem,m,rem)):
        if count==0:
            continue
        S = (d-1)**2*(l-1)+n-l
        T = (d-1)**3*(l-1)+n-l
        # Drift is r-v*t; r runs over r0,...,r0+count-1 and 0<=r<=v.
        v = n+d-1-d*l
        r1 = r0+count-1
        s1 = (r0+r1)*count//2
        s2 = r1*(r1+1)*(2*r1+1)//6 - (r0-1)*r0*(2*r0-1)//6
        drift = F(2*s2-2*v*s1+count*v*v,2*v) if v else F(0)
        err = (F(2*count*T,3*S)+drift)*l/2
        lo += F(l*count,16)*sqrt_out(2*PI_LO*S,False)-err
        hi += F(l*count,16)*sqrt_out(2*PI_HI*S,True)+err
    return lo,hi


def exclusion(n,d):
    D = max(payoff(n,d),cut_bound(n,d),stein_interval(n,d)[0])
    Q = max(2, 1+(2*D)//n)
    degree = min(n,2*Q-1)
    entropy_nats = log_bounds(F(n,degree))[0] - (1+log_bounds(degree)[1])/degree - 2*D/(n*(Q-1))
    bits = entropy_nats/LN2[entropy_nats>=0]
    # Rounding down to a thousandth of a bit per key weakens the lower bound.
    milli = (1000*bits)//1
    bits = F(milli,1000)
    H = (D-n+1)//(50*n - n*bits - n+1)
    assert 2*F(H,Q-1) < LN2[0]
    bound = n*bits+n-1+(D-n+1)/H
    assert bound >= 50*n
    return d, D//1, Q, milli, H, bound//1


def test():
    pairs=0
    arrays=0
    for n in range(2,11):
        for m in range(1, n//2+1):
            numerator=0; count=0
            for pool in combinations(range(n),2*m):
                for r in combinations(range(2*m),m):
                    s = sorted(set(range(2*m))-set(r))
                    numerator += sum(abs(pool[i]-pool[j]) for i,j in zip(r,s))
                    count += 1
            expected = F(2*(n+1),2*m+1)*exact_bridge(m)
            assert F(numerator,count)==expected
            pairs += count
        if n>8:
            continue
        ans = [0]*(n+1); nf=0
        for a in permutations(range(n)):
            nf+=1
            for d in range(2,n+1):
                ans[d] += sum(abs(i-v) for r in range(d) for i,v in
                              zip(range(r,n,d), sorted(a[r::d])))
        arrays += nf*(n-1)
        for d in range(2,n+1):
            low,high = stein_interval(n,d)
            assert low<=F(ans[d],2*nf)<=high
            if 2*((n+d-1)//d)>n:
                continue
            assert F(ans[d],2*nf) >= payoff(n,d)
            if d==2 and not n%2:
                assert F(ans[d],2*nf)==exact_bridge(n//2)
    for n in [96,191,249,512,1537]:
        for d in [2,3,4,5,9,16,31]:
            m,r = divmod(n,d)
            N = d*m
            exact = F(0)
            for j in range(1,m):
                mass=F(comb(m,j)*comb((d-1)*m,(d-1)*j),comb(N,d*j))
                exact += F((d-1)*j*(m-j),m)*mass
            assert cut_bound(n,d) <= max(F(0),d*exact-F(N*(d-1),2)-r*n)
    direct=0
    for n in (47,80,129,201):
        for d in (2,3,4,7,13,28):
            exact=F(0)
            for r in range(d):
                l=len(range(r,n,d))
                num=0
                for k in range(l):
                    for j in range(k,n-l+k+1):
                        num += abs(r+d*k-j)*comb(j,k)*comb(n-1-j,l-1-k)
                exact += F(num,2*comb(n,l))
            lo,hi=stein_interval(n,d)
            assert lo<=exact<=hi
            assert cut_bound(n,d)<=exact
            if 2*((n+d-1)//d)<=n:
                assert payoff(n,d)<=exact
            direct+=1
    print("ordered disjoint subset pairs",pairs,"permutation/gap pairs",arrays,
          "exact medium full means",direct)


if __name__=="__main__":
    test()
    print("divisor, D_floor, Q, prefix_dual_millibits, H_max_excluded, lower_comparisons_rounded_down")
    for d in (2,3,4,5,7,8,10,16,25,100,1000,10000,1000000,500000000):
        print(*exclusion(10**9,d),sep=",")
