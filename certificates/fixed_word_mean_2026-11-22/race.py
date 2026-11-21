"""Exact full fixed-word mean via ordered Boolean decision diagrams and polynomial integration."""
from collections import Counter
from fractions import Fraction
from functools import cache
from math import factorial


class Decisions:
    def __init__(self,n,order=None):
        self.n=n
        self.nodes=[(n,0,0),(n,1,1)]
        self.unique={}
        order=tuple(range(n)) if order is None else tuple(order)
        if sorted(order)!=list(range(n)):
            raise ValueError("invalid variable order")
        self.slots=[self.make(order.index(i),0,1) for i in range(n)]
        self.operations={}

    def make(self,r,lo,hi):
        if lo==hi:
            return lo
        k=(r,lo,hi)
        if k not in self.unique:
            self.unique[k]=len(self.nodes)
            self.nodes.append(k)
        return self.unique[k]

    def branches(self,a,b):
        ra,al,ah=self.nodes[a]
        rb,bl,bh=self.nodes[b]
        r=min(ra,rb)
        return r,(al,ah) if ra==r else (a,a),(bl,bh) if rb==r else (b,b)

    def combine(self,a,b,is_or):
        if a==b:
            return a
        if a>b:
            a,b=b,a
        if a<2:
            return (b if a==0 else 1) if is_or else (0 if a==0 else b)
        key=(a,b,is_or)
        if key not in self.operations:
            r,(al,ah),(bl,bh)=self.branches(a,b)
            self.operations[key]=self.make(r,self.combine(al,bl,is_or),self.combine(ah,bh,is_or))
        return self.operations[key]


def poly_mix(lo,hi,plus=(),minus=()):
    """(1-t)lo+t*hi+plus-minus in integer power coefficients."""
    a=[0]*max(len(lo)+1,len(hi)+1,len(plus),len(minus))
    for i,x in enumerate(lo):
        a[i]+=x
        a[i+1]-=x
    for i,x in enumerate(hi):
        a[i+1]+=x
    for i,x in enumerate(plus):
        a[i]+=x
    for i,x in enumerate(minus):
        a[i]-=x
    while a and a[-1]==0:
        a.pop()
    return tuple(a)


class Races:
    def __init__(self,diagram):
        self.diagram=diagram
        self.joint=cache(self._joint)
        self.derivative=cache(self._derivative)
        self.prob=cache(self._prob)

    def _joint(self,a,b):
        # Diagonal probability at t: output a above threshold, b below it.
        if a==1 or b==0 or a==b:
            return ()
        if a==0 and b==1:
            return (1,)
        _,(al,ah),(bl,bh)=self.diagram.branches(a,b)
        return poly_mix(self.joint(al,bl),self.joint(ah,bh))

    def _derivative(self,a,b):
        # Never prune a==b: increasing only b's threshold separates tied values.
        if a==1 or b<2:
            return ()
        _,(al,ah),(bl,bh)=self.diagram.branches(a,b)
        return poly_mix(self.derivative(al,bl),self.derivative(ah,bh),
                        self.joint(al,bh),self.joint(al,bl))

    def _prob(self,a,b):
        return sum((Fraction(x,j+1) for j,x in enumerate(self.derivative(a,b))),Fraction())

    def clear(self):
        for fn in (self.joint,self.derivative,self.prob):
            fn.cache_clear()


def symbolic_mean(n,gaps,order=None):
    """Return per-pass means (shifts, compares), and symbolic work counts."""
    if any(not 0<h<n for h in gaps):
        raise ValueError("gap out of range")
    diagram=Decisions(n,order)
    races=Races(diagram)
    state=diagram.slots[:]
    ledger=[]
    for p,h in enumerate(gaps):
        moves,stops=Counter(),Counter()
        for r in range(h):
            chain=state[r::h]
            prefix_min=0
            for i,x in enumerate(chain):
                for y in chain[:i]:
                    moves[y,x]+=1
                if i:
                    stops[x,prefix_min]+=1
                prefix_min=diagram.combine(prefix_min,x,True)
            if p+1==len(gaps):
                continue
            # Fixed insertion network producing order-statistic output bits.
            for i in range(1,len(chain)):
                for j in range(i,0,-1):
                    a,b=chain[j-1],chain[j]
                    chain[j-1]=diagram.combine(a,b,True)
                    chain[j]=diagram.combine(a,b,False)
            state[r::h]=chain
        m=sum((count*races.prob(*k) for k,count in moves.items()),Fraction())
        s=sum((count*races.prob(*k) for k,count in stops.items()),Fraction())
        ledger.append((m,m+s))
    stats=(len(diagram.nodes),races.joint.cache_info().currsize,
           races.derivative.cache_info().currsize)
    assert all((x*factorial(n)).denominator==1 for pair in ledger for x in pair)
    races.clear()
    return ledger,stats


if __name__=="__main__":
    import sys
    n=int(sys.argv[1])
    gaps=list(map(int,sys.argv[2:]))
    ledger,stats=symbolic_mean(n,gaps)
    for h,(m,c) in zip(gaps,ledger):
        print("gap",h,"shifts",m,"comparisons",c)
    print("total",sum(c for m,c in ledger),"nodes / joint / derivative states",*stats)
