"""Directed rational certificates for uniform finite Shellsort exclusions."""
from fractions import Fraction as F
from functools import cache
from itertools import combinations
from math import comb,isqrt

N=10**9
TARGET=50*N
PRECISION=10**22


def atanh_log(u):
    v=(u-1)/(u+1)
    power=v
    partial_sum=F(0)
    for j in range(32):
        partial_sum+=2*power/(2*j+1)
        power*=v*v
    upper=partial_sum+2*power/(65*(1-v*v))
    return partial_sum,upper


LOG2=atanh_log(F(2))


@cache
def log_interval(x):
    x=F(x)
    k=x.numerator.bit_length()-x.denominator.bit_length()
    u=x/F(2)**k
    if u<1:
        u*=2
        k-=1
    assert 1<=u<2
    lo,hi=atanh_log(u)
    a,b=LOG2 if k>=0 else LOG2[::-1]
    lo+=k*a
    hi+=k*b
    return F((lo*PRECISION)//1,PRECISION),F(-((-hi*PRECISION)//1),PRECISION)


def divide_lower(z,w):
    return z/(w[1] if z>=0 else w[0])


def chain_statistics(limit):
    harmonic=F(0)
    log_factorial_upper=F(0)
    result={}
    for length in range(1,limit+1):
        harmonic+=F(1,length)
        log_factorial_upper+=log_interval(length)[1]
        result[length]=(F(length-1,4)+1-harmonic/length,log_factorial_upper/length)
    return result


def entropy_sieve(ln_factorial_per_key):
    active_limit=11_000_000
    m=2*active_limit
    log_factorial_upper=(m+1)*log_interval(m)[1]-m+1
    suffix=divide_lower(N*ln_factorial_per_key-log_factorial_upper,log_interval(2))
    slack=TARGET-suffix
    max_prefix=(isqrt(int(1+8*slack))-1)//2
    if F(max_prefix*(max_prefix+1),2)>=slack:
        max_prefix-=1
    assert F(max_prefix*(max_prefix+1),2)<slack<=F((max_prefix+1)*(max_prefix+2),2)
    assert max_prefix<active_limit
    upper=max_prefix+(TARGET-F(max_prefix*(max_prefix+1),2))/(active_limit+1)
    excluded=-((-upper)//1)
    print("length_at_least",excluded,"excluded with cutoff",N-active_limit,
          "suffix_entropy_comparisons",int(suffix))


def active_prefix_sieve(ln_factorial_per_key):
    input_bits=int(divide_lower(N*ln_factorial_per_key,log_interval(2)))
    slack=TARGET-input_bits

    def extra_capacity(scan):
        # Integer upper bound on log2((2 scan)!) minus that pass's scan.
        r=(2*scan-1).bit_length()
        return 2*scan*r-((1<<r)-1)-scan

    last=0
    spent=0
    passes=0
    while last<N-1:
        target=spent-slack
        if extra_capacity(last+1)>target:
            trial=last+1
        else:
            if extra_capacity(N-1)<=target:
                break
            lo,hi=last,N-1
            while hi-lo>1:
                c=(hi+lo)//2
                if extra_capacity(c)>target:
                    hi=c
                else:
                    lo=c
            trial=hi
        if spent+trial>=TARGET:
            print("active_prefix_excludes_length_at_least",passes+1,"prefix_cost_before_failure",
                  spent,"forced_next_scan",trial,"input_bits_lower",input_bits)
            return
        last=trial
        spent+=trial
        passes+=1
    raise AssertionError("the recurrence did not reach the spending limit")


def gap_score(g,t):
    """Lower bound on C contribution after subtracting the log-partition."""
    den=log_interval(1/t)
    remaining=N-g
    logz=(N-g)*log_interval(1/(1-t))[1]
    for j in range(1,18):
        count=min(g,max(0,N-j*g))
        logz+=count*log_interval(1+(1-2*t)*t**(j-1))[1]
        remaining-=count
    logz+=remaining*(1-2*t)*t**17
    return N-g+divide_lower(-logz,den)


def count_sieve(ln_factorial_per_key):
    counts=((1_000_000,44,7),(10_000_000,44,10),(20_000_000,45,7),(50_000_000,47,6),
            (100_000_000,50,7),(200_000_000,59,2),(300_000_000,70,1),(500_000_000,107,1))
    for g,k,i in counts:
        t=F(i,100)
        score=divide_lower(N*ln_factorial_per_key,log_interval(1/t))+(k-1)*gap_score(g,t)+gap_score(1,t)
        assert score>TARGET,(g,k,i)
        print("gap_count_at_least",k,"with gaps_at_most",g,"lower",int(score))


def incomplete_certificate_witness():
    word=[]
    a=1
    while a<N:
        b=a
        while b<N:
            word.append(b)
            b*=13
        a*=11
    word=sorted(set(word),reverse=True)
    g=word[0]
    lengths=chain_statistics(N//g+1)
    k,r=divmod(N,g)
    counts=((k,k*(g-r)),(k+1,(k+1)*r))
    head_cost=sum(lengths[length][0]*count for length,count in counts)
    head_entropy=sum(count*sum(log_interval(i)[0] for i in range(1,length+1))/length
                     for length,count in counts)
    suffix_insertions=sum(N-h for h in word[1:])
    trial_entropy=head_entropy+suffix_insertions*(log_interval(F(5,4))[0]*F(4,5)+log_interval(5)[0]*F(1,5))
    trial_mean=head_cost+F(6,5)*suffix_insertions
    hn_upper=(N+1)*log_interval(N)[1]-N+1
    assert trial_entropy>hn_upper
    assert trial_mean<TARGET
    print("product_11_13 trial_coordinate_law",len(word),"passes","largest_gap",g,
          "entropy_lower",int(trial_entropy),"input_entropy_upper",int(hn_upper),
          "mean_upper",-((-trial_mean)//1))


def second_pass_cost(m):
    # The sorted parity rows contain m keys each. Count uniform color paths.
    total=0
    for ell in range(m):
        for a in range(m+1):
            count=comb(ell+a,a)*comb(2*m-ell-a-1,m-a)
            total+=count*(max(0,ell+1-a)+max(0,ell-a))
    shifts=F(total,comb(2*m,m))
    return shifts+2*m-F(3,2)


def check_two_color_sum():
    for m in range(1,6):
        s=0
        for red in combinations(range(2*m),m):
            blue=sorted(set(range(2*m))-set(red))
            row=[x for keys in zip(red,blue) for x in keys]
            for j in range(1,len(row)):
                moves=sum(value>row[j] for value in row[:j])
                s+=moves+int(moves<j)
        assert F(s,comb(2*m,m))==second_pass_cost(m)


def exact_two_pass_relaxation_barrier():
    check_two_color_sum()
    word=(50_000_000,25_000_000,1_000_003,100_003,10_007,1009,101,1)
    m=20
    natural_head=chain_statistics(m)[m][0]*N+second_pass_cost(m)*F(N,2*m)
    head_entropy=F(N,2*m)*sum(log_interval(j)[0] for j in range(1,2*m+1))
    tail=word[2:]
    suffix_insertions=sum(N-h for h in tail)
    covered=sum(N-64*h for h in tail)
    t=F(6,7)
    norm=sum(t**j for j in range(64))
    mean=sum(j*t**j for j in range(64))/norm
    entropy=log_interval(norm)[0]+mean*log_interval(1/t)[0]
    input_entropy_upper=(N+1)*log_interval(N)[1]-N+1
    trial_entropy_lower=head_entropy+covered*entropy
    trial_cost_upper=natural_head+suffix_insertions+covered*mean
    assert trial_cost_upper<TARGET
    assert trial_entropy_lower>input_entropy_upper
    print("eight_pass_two_real_head trial_coordinate_law","head_mean_upper",-((-natural_head)//1),
          "trial_entropy_lower",int(trial_entropy_lower),"input_entropy_upper",int(input_entropy_upper),
          "trial_mean_upper",-((-trial_cost_upper)//1))


def eight_pass_first_gap(ln_factorial_per_key,lengths):
    t=F(96,125)
    den=log_interval(1/t)
    penalty=7*log_interval(1-t)[0]
    assert F(1,76)<den[0]/4
    def f(k):
        c,h=lengths[k]
        return c+7+divide_lower(ln_factorial_per_key+penalty-h,den)
    def mix(g):
        k,r=divmod(N,g)
        assert k==76
        return f(k)*k*(g-r)+f(k+1)*(k+1)*r
    assert f(77)*N>TARGET
    lo,hi=N//77+1,N//76+1
    assert mix(lo)>TARGET and hi-lo>1
    while hi-lo>1:
        c=(hi+lo)//2
        if mix(c)>TARGET:
            lo=c
        else:
            hi=c
    print("eight_or_fewer_passes first_gap_at_most",lo,"lower",int(mix(lo)))


def eight_pass_high_second(ln_factorial_per_key,lengths):
    t=F(7,8)
    den=log_interval(1/t)
    penalty=6*log_interval(1-t)[0]
    first_profiles=[]
    second_profiles=[]
    for length in range(1,6):
        cost,entropy_upper=lengths[length]
        entropy_lower=sum(log_interval(i)[0] for i in range(1,length+1))/length
        decrease=(-entropy_upper/den[0],-entropy_lower/den[1])
        first_profiles.append((cost+decrease[0],cost+decrease[1]))
        scans=1-F(1,length)
        second_profiles.append((scans+decrease[0],scans+decrease[1]))
    assert all(a[0]>b[1] for profiles in (first_profiles,second_profiles) for a,b in zip(profiles,profiles[1:]))
    constant=6+divide_lower(ln_factorial_per_key+penalty,den)
    def floor_bound(g):
        k,r=divmod(N,g)
        short=(first_profiles[k-1][0]+second_profiles[k-1][0])*k*(g-r)
        long=(first_profiles[k][0]+second_profiles[k][0])*(k+1)*r
        return constant*N+short+long
    lo,hi=N//5+1,N//4
    assert floor_bound(lo)<TARGET<floor_bound(hi)
    while hi-lo>1:
        c=(hi+lo)//2
        if floor_bound(c)>TARGET:
            hi=c
        else:
            lo=c
    print("eight_or_fewer_passes second_gap_at_least",hi,"lower",int(floor_bound(hi)))


def main():
    t=F(431,500)
    ln_factorial_per_key=log_interval(N)[0]-1
    lengths=chain_statistics(201)
    den=log_interval(1/t)
    penalty=6*log_interval(1-t)[0]
    short=min((c+6+divide_lower(ln_factorial_per_key+penalty-h,den),length)
              for length,(c,h) in lengths.items())
    assert short[0]>F(50017,1000)
    print("pass_count_at_most_7 lower_if_first_chain_length_at_most_201",
          int(N*short[0]),"min_length",short[1])
    # For longer chains the first pass itself contributes strictly more than
    # 50.017 comparisons per key, including the case of length exactly 201.
    assert lengths[201][0]>F(50017,1000)

    t=F(1,2)
    den=log_interval(1/t)
    g=9_558_064
    length,long_count=divmod(N,g)
    def f(k):
        c,h=lengths[k]
        return c+divide_lower(ln_factorial_per_key-h,den)
    def mix(g):
        k,r=divmod(N,g)
        return f(k)*k*(g-r)+f(k+1)*(k+1)*r
    assert length==104 and long_count>0
    assert mix(g)>TARGET
    assert log_interval(105)[1]/105<log_interval(2)[0]/4
    print("first_gap_at_most",g,"lower",int(mix(g)),"strictly_above_target",mix(g)>TARGET)
    entropy_sieve(ln_factorial_per_key)
    active_prefix_sieve(ln_factorial_per_key)
    count_sieve(ln_factorial_per_key)
    incomplete_certificate_witness()
    exact_two_pass_relaxation_barrier()
    eight_pass_first_gap(ln_factorial_per_key,lengths)
    eight_pass_high_second(ln_factorial_per_key,lengths)


if __name__=="__main__":
    main()
