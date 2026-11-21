"""Certified pass-by-pass fits for multiplicative gap tables, no permutation samples."""
from functools import cache
from itertools import combinations
from math import gcd
from pathlib import Path
import sys

sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'billion_theory_2026-11-22'/'structure'))
from final_pass import graph

@cache
def kernel(gens,target=1):
    edges,n,missing=graph(gens)
    edges=[(i,j,sum(d%target==0 for d in ds),sz,
            any((mask>>(z-d))&1 for d in range(target,z+1,target)),z)
           for i,j,ds,sz,_,mask,z in edges]
    prev=[None]*n
    prev[0]=0
    history=[]
    seen={}
    while True:
        t=len(history)
        history.append(prev[0])
        if None not in prev and t>=len(missing)+target:
            normalized=tuple(x-prev[0] for x in prev)
            if normalized in seen:
                a=seen[normalized]
                return history, a, t-a, prev[0]-history[a]
            seen[normalized]=t
        row=[None]*n
        for i,j,m,sz,below,z in edges:
            if prev[i] is not None:
                cut=t-sz
                c=prev[i]+m+int((cut+z)%target < cut or below)
                if row[j] is None or row[j]<c:
                    row[j]=c
        prev=row

def cap(gens,length,target=1):
    v,a,p,d=kernel(gens,target)
    if length<len(v):
        return v[length]
    q,r=divmod(length-a,p)
    return v[a+r]+q*d

def smooth(n,gens):
    found={1}
    for g in gens:
        for h in list(found):
            while h*g<n:
                h*=g
                found.add(h)
    return sorted(found,reverse=True)

def total(n,gens):
    word=smooth(n,gens)
    c=0
    for h in word:
        l,r=divmod(n,h)
        c+=(h-r)*cap(gens,l)+r*cap(gens,l+1)
    return c,len(word)

if __name__=='__main__':
    n=10**9
    for a,b in combinations(range(2,10),2):
        if gcd(a,b)==1 and a+b<=15:
            g=(a,b)
            print(g,*total(n,g),flush=True)
