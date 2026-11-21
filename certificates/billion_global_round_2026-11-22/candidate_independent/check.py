"""Exact small-chain tests and finite constants for the local pricing barrier."""

from fractions import Fraction as F
from itertools import combinations, permutations
from legal_prices import N, SMOOTH, allowed_distances, ceil, logs, weighted


def subsets(population):
    return (d for size in range(len(population)+1) for d in combinations(population,size))


def exhaustive():
    families=0
    permutations_per_tilt=0
    for length in range(1,8):
        data=[]
        for order in permutations(range(length)):
            distances={j-i for j in range(length) for i in range(j) if order[i]>order[j]}
            moves=[sum(order[i]>order[j] for i in range(j)) for j in range(length)]
            extra=sum(min(m,j-1) for j,m in enumerate(moves) if j)
            data.append((distances,extra))
        for d in subsets(range(1,length)):
            families+=1
            for t in (F(1,8),F(3,4),F(9,16)):
                mass=sum(t**e for s,e in data if s.isdisjoint(d))
                all_records=sum(t**e for _,e in data)
                assert weighted(length,d,t)==mass/all_records,(length,d,t)
            permutations_per_tilt+=len(data)
    return families,permutations_per_tilt


def barrier():
    t=F(1,8)
    p=F(63,500)
    epsilon=F(1,512)+F(1,1<<30)
    fail=5*p**4+5*epsilon
    cap=F(3,250)
    assert t+(1-2*t)*t**4<=p
    assert t**3*(1+t**7)==epsilon
    assert fail<cap
    assert F(1,2)*F(1,5)**3<cap
    assert epsilon<cap/5
    assert len(SMOOTH)==45
    assert all(N//h+(N%h!=0)<=11 for h in SMOOTH[:9])
    for i in range(10,13):
        d=allowed_distances(N,SMOOTH[:i],SMOOTH[i])
        assert min(d)==11
    bound=F(36*N,5)*logs(1/(1-cap))[1]/logs(1/t)[0]
    assert bound<42_000_000
    window_fail=10*F(1,2)*F(1,5)**8
    pair_good=(1-epsilon)*(1-window_fail)
    correlated_event_bound=F(36*N)*logs(1/pair_good)[1]/logs(1/t)[0]
    assert correlated_event_bound<35_000_000
    return ceil(bound),ceil(correlated_event_bound)


def nonzero(q,t):
    if not q:
        return F(0)
    eq=(1-2*t)*t**(q-1)
    return (t+eq)/(1+eq)


def window_legal(t,a,r):
    # P(at least r zero digits) on a window of ten, with exact digit marginals.
    pmf=[F(1)]
    for q in range(a,a+10):
        p=1-nonzero(q,t)
        pmf=[x+y for x,y in zip(
            [m*(1-p) for m in pmf]+[0],
            [0]+[m*p for m in pmf])]
    return sum(pmf[r:])


def sharper_window_barrier():
    t=F(1,8)
    candidates=[]
    for r in range(1,10):
        inc=F(0)
        tail=t**(r+1)*(1+t**(9-r))
        tail_price=logs(1/(1-tail))[1]
        window_prices=[logs(1/window_legal(t,a,r))[1] for a in range(1,18)]
        for h in SMOOTH:
            length,extra=divmod(N,h)
            for l,mult in ((length,h-extra),(length+1,extra)):
                k=max(0,l-11)
                inc+=mult*(k*tail_price+sum(window_prices[:min(k,16)])+
                           max(0,k-16)*window_prices[-1])
        candidates.append((ceil(inc/logs(1/t)[0]),r))
    cap,r=min(candidates)
    assert cap<1_300_000
    return cap,r


if __name__=="__main__":
    cases,total=exhaustive()
    print("number of (length, constraints) cases",cases)
    print("permutation/constraints pairs per tilt",total)
    print("exact tilts",3)
    block,windows=barrier()
    print("maximum cost-bound improvement from local legal support, independent blocks",block)
    print("maximum cost-bound improvement from local legal support, associated windows",windows)
    print("strongest sliding-window cap and selected zero count",*sharper_window_barrier())
