#!/usr/bin/env python3
"""Exact finite certificate for the sharpened P04 spectral constants.

The infinite-scale menu argument is analytic: for c >= 944, inclusion-
exclusion gives |G| >= 164*c/375 - 124/15 >= 3*c/7.  This program
checks the finite seed exceptions and the stated rational calibration.
It does not replace the Fourier/large-sieve proof with numerical testing.
"""
from fractions import Fraction as F
from math import gcd
from pathlib import Path
import argparse
import json


def next_seed(c):
    return (107*c + 94)//50


def certificate():
    seeds=[1]
    while seeds[-1] < 5000:
        seeds.append(next_seed(seeds[-1]))
    rows=[]
    for j,c in enumerate(seeds[:-2]):
        if c >= 944:
            break
        g2,g1=seeds[j+1],seeds[j+2]
        lo,hi=(c+1)//2,107*c//50
        menu=[h for h in range(lo,hi+1) if gcd(h,gcd(g1,g2))==1]
        rows.append({'c':c,'g1':g1,'g2':g2,'gcd':gcd(g1,g2),
                     'lo':lo,'hi':hi,'menu_size':len(menu)})
        assert 7*len(menu) >= 3*c
        assert menu and all(0<h<g2<g1 for h in menu)
        if j:
            assert min(menu) > seeds[j-1]
        else:
            assert menu == [1]
        if c <= 111:
            assert g1 <= 10*c
            assert max(menu) < 3*c
        else:
            assert c >= 239
            assert 5*g1 <= 23*c

    # Ancillary exact check of the elementary small-modulus bounds.
    for g in range(1,95):
        phi=sum(gcd(a,g)==1 for a in range(1,g+1))
        assert 15*phi >= 4*g
    assert F(164,375)*944-F(124,15) >= F(3,7)*944
    assert F(164,375) > F(3,7)
    assert seeds[8] == 1099

    # Retained-gap ratio at the only exceptional seed >= 239.
    assert next_seed(next_seed(239)) == 1099
    assert 5*1099 <= 23*239
    assert F(11449,2500)*290+F(7379,1250) <= F(23,5)*290
    assert F(11449,2500) < F(23,5)

    M,H,R=F(7,3),F(107,50),F(23,5)
    D,m=460000,56
    alpha=(2*m-1)*M*4*H/D+F(4*(1+D*D),2**m)
    beta=M*H*R*D+(2*m-1)*M*(8*H*H+4*H/D)+2*H
    assert alpha < F(1,200)
    assert beta < 2**24
    assert alpha == F(31278107868329998287,6473924464345088000000)
    assert beta == F(182425417976339,17250000)
    assert 3*111 < D
    assert 60*111**2 == 739260
    assert 739260 < 2**24

    return {
        'passed':True,
        'exact_arithmetic':True,
        'menu_lower_coefficient':'3/7',
        'menu_exception_rows':rows,
        'D':D,'m':m,
        'M':str(M),'H':str(H),'R_large_seed':str(R),
        'large_sieve_reference':'Montgomery and Vaughan (1973), Theorem 1',
        'alpha_exact':str(alpha),
        'alpha_budget':'1/200',
        'beta_exact_at_R':str(beta),
        'beta_budget':2**24,
        'alpha_slack':str(F(1,200)-alpha),
        'beta_slack':str(2**24-beta),
        'small_seed_beta_upper':60*111**2,
        'scope':'Finite menu exceptions and rational constants; Analytic proof: manuscript Sections 4 and 5.'
    }


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    data=certificate()
    text=json.dumps(data,ensure_ascii=False,indent=2)+'\n'
    if args.output:
        args.output.write_text(text)
    print(text)
