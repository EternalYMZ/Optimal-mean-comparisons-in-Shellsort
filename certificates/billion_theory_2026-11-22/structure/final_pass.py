"""Exact worst unit-pass comparisons after a sorted coprime gap prefix."""
from collections import deque
from itertools import permutations
from pathlib import Path
import json


def holes(gaps):
    seen=[True]
    while len(seen)<=max(gaps) or not all(seen[-min(gaps):]):
        i=len(seen)
        seen.append(any(i>=g and seen[i-g] for g in gaps))
    return [i for i,x in enumerate(seen) if not x]


def graph(gaps):
    missing=holes(gaps)
    queue=deque([0])
    ids={0:0}
    edges=[]
    while queue:
        mask=queue.popleft()
        for z in [0]+missing:
            bit=1<<z
            if mask & bit or any(z>=g and not mask&(bit>>g) for g in gaps):
                continue
            enlarged=mask|bit
            skip=(~enlarged & (enlarged+1)).bit_length()-1
            after=enlarged>>skip
            if after not in ids:
                ids[after]=len(ids)
                queue.append(after)
            below=(mask & (bit-1)).bit_count()
            distances=tuple(d for d in range(1,z+1) if not mask&(1<<(z-d)))
            edges.append((ids[mask],ids[after],distances,mask.bit_count(),below,mask,z))
    return edges,len(ids),missing


def certificate(gaps=(4,10,23),n=10**9,tail=None):
    edges,vertices,missing=graph(gaps)
    edges=[(i,j,len(ds) if tail is None else sum(d>tail for d in ds),sz,below)
           for i,j,ds,sz,below,_,_ in edges]
    f=[None]*vertices
    f[0]=0
    history=[]
    normalized={}
    t=0
    while t<=n:
        history.append(f[0])
        if t>len(missing) and None not in f:
            key=tuple(x-f[0] for x in f)
            if key in normalized:
                a=normalized[key]
                p=t-a; gain=f[0]-history[a]
                k,r=divmod(n-a,p)
                return dict(gaps=gaps,n=n,missing=missing,vertices=vertices,edges=len(edges),
                            from_step=a,repeat_step=t,period=p,gain=gain,
                            base_answers=history[a:t],exact=history[a+r]+k*gain)
            normalized[key]=t
        step=[None]*vertices
        for i,j,inv,sz,below in edges:
            if f[i] is None:continue
            score=f[i]+inv+int(tail is None and (t-sz>0 or below>0))
            if step[j] is None or step[j]<score:step[j]=score
        f=step;t+=1
    return dict(exact=history[n])


def count(arr):
    a=list(arr)
    c=0
    for i in range(1,len(a)):
        j=i; x=a[i]
        while j>0:
            c+=1
            if x>a[j-1]:break
            a[j]=a[j-1]; j-=1
        a[j]=x
    return c


if __name__=='__main__':
    for gaps in ((3,4),(4,10,23),(4,5),(3,7)):
        for n in range(1,9):
            observed=max(count(p) for p in permutations(range(n))
                         if all(p[i]<p[i+h] for h in gaps for i in range(n-h)))
            assert observed==certificate(gaps,n)['exact']
    result=certificate()
    result['long_pairs']={d:certificate(tail=d)['exact'] for d in result['missing']}
    print(json.dumps(result))
    Path(__file__).with_name('final_pass.json').write_text(json.dumps(result,indent=2)+'\n')
