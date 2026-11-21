from fractions import Fraction
from itertools import combinations,permutations
from math import factorial
from race import symbolic_mean


def exhaustive(n,word):
    total=[[0,0] for _ in word]
    for perm in permutations(range(n)):
        a=list(perm)
        for j,h in enumerate(word):
            for k in range(h,n):
                while k>=h:
                    total[j][1]+=1
                    if a[k]>a[k-h]:
                        break
                    a[k-h],a[k]=a[k],a[k-h]
                    total[j][0]+=1
                    k-=h
    return [tuple(Fraction(x,factorial(n)) for x in v) for v in total]


if __name__=="__main__":
    words=[(n,tuple(reversed(g))) for n in range(2,8) for p in range(1,n)
           for g in combinations(range(1,n),p)]
    words.extend([(8,(7,5,3,1)),(8,(6,4,3,2,1)),(9,(7,6,4,1)),
                  (7,(1,3,2,1)),(7,(4,2,4,2,1))])
    for n,word in words:
        exact=exhaustive(n,word)
        for order in (None,range(n-1,-1,-1)):
            assert symbolic_mean(n,word,order)[0]==exact,(n,word)
    print("words",len(words),"input/word pairs",sum(factorial(n) for n,w in words),
          "two variable orders; all individual shift and comparison means agree")
