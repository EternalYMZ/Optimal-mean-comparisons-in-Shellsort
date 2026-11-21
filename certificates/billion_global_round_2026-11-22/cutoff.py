"""Upper limits on how many small gaps any passing table can contain."""
from fractions import Fraction as F
from functools import cache
from pathlib import Path
import sys

work=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(work/"billion_joint_2026-11-22"/"family"))
from records import logs

N=10**9


@cache
def coefficients(t):
    a=1-2*t
    # Sum log(1+a*t**j), retaining the terms that matter at these prices.
    correction=sum(logs(1+a*t**j)[1] for j in range(12))
    correction+=a*t**12/(1-t)
    return logs(1/(1-t))[1],correction,*logs(1/t)


def lower_per_key(rho,count,t):
    peak,correction,log_low,log_high=coefficients(t)
    visits=1-rho
    num=logs(N)[0]-1-count*(visits*peak+rho*correction)
    return count*visits+num/(log_high if num>=0 else log_low)


if __name__=="__main__":
    prices=[F(q,200) for q in range(1,100)]
    for cap in (1_000_000,10_000_000,25_000_000,50_000_000,100_000_000,200_000_000,250_000_000):
        rho=F(cap,N)
        for count in range(1,101):
            lower,t=max((lower_per_key(rho,count,t),t) for t in prices)
            if lower>=50:
                visits=(50/(1-rho))
                print(cap,"number excluded",count,"integer mean lower",(N*lower)//1,
                      "t",t,"scan-only threshold",-(-visits.numerator//visits.denominator))
                break
