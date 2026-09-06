#!/usr/bin/env python3
"""Exact finite regression checks. These neither execute Lean nor prove limits."""
from __future__ import annotations
import argparse
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product
import json
from math import comb, gcd, prod
from pathlib import Path
from random import Random
from time import perf_counter


def factor(n: int) -> dict[int,int]:
    out = {}; p = 2
    while p*p <= n:
        while n % p == 0:
            out[p] = out.get(p,0)+1; n //= p
        p += 1
    if n > 1: out[n] = out.get(n,0)+1
    return out


def primes(w: int) -> list[int]:
    return [p for p in range(2,w+1) if all(p % d for d in range(2,int(p**0.5)+1))]


def tau(n: int) -> int:
    return prod(e+1 for e in factor(n).values()) if n else 0


def harmonic(n: int) -> F:
    return sum((F(1,j) for j in range(1,n+1)),F(0))


def residue_count(q: int, u: int, h: int, r: int) -> int:
    """Integer points u < m <= u+h in the residue class r mod q."""
    return (u+h-r)//q-(u-r)//q


def exact_linear_survivors(c: int, u: int, h: int, w: int) -> int:
    pp = [p for p in primes(w) if c % p]
    answer = 0
    for mask in range(1 << len(pp)):
        d = prod(pp[j] for j in range(len(pp)) if (mask >> j)&1)
        r = pow(c,-1,d) if d > 1 else 0
        answer += (-1)**mask.bit_count()*residue_count(d,u,h,r)
    return answer


def run() -> dict:
    counts = Counter(); rng = Random(20260906); started = perf_counter()
    for q in range(1,33):
        for u in (0,1,7,35):
            for h in (0,1,2,9,31,64):
                for r in range(q):
                    c = residue_count(q,u,h,r)
                    assert h//q <= c <= h//q+1
                    assert abs(F(c)-F(h,q)) <= 1
                    counts['residue_error_cases'] += 1
    for size in range(7):
        for trial in range(12):
            xx = [F(rng.randrange(6),5) for _ in range(size)]
            exact = prod(1-x for x in xx)
            doubled = prod(1+2*x for x in xx)
            for k in range(size+3):
                trunc = sum(((-1)**len(s)*prod(xx[i] for i in s)
                    for j in range(min(k,size)+1) for s in combinations(range(size),j)),F(0))
                assert (-1)**k*(trunc-exact) >= 0
                assert abs(trunc-exact) <= doubled/F(2**(k+1))
                counts['bonferroni_cases'] += 1
    for w in range(2,18):
        k = 8*w.bit_length()
        length = 4*w**(k+2)
        for c in (3,4,12,35,210):
            v = prod((1-F(1,p) for p in primes(w) if c % p),start=F(1))
            for u in (0,13):
                for h in (0,5,length,length+19):
                    s = exact_linear_survivors(c,u,h,w)
                    assert abs(F(s)-h*v) <= w**(k+1)+F(h*w*w,2**(k+1))
                    if h >= length:
                        assert h*v/2 <= s <= 3*h*v/2
                        counts['relative_sieve_cases'] += 1
                    if h < 100:
                        brute = sum(all((c*m-1)%p for p in primes(w)) for m in range(u+1,u+h+1))
                        assert s == brute
                    counts['absolute_sieve_cases'] += 1
    ht = F(0); d8sum=0; tausum=0
    for n in range(1,501):
        fac = factor(n); d8 = prod(comb(e+7,7) for e in fac.values())
        assert tau(n)**3 <= d8
        ht += F(1,n); d8sum += d8; tausum += tau(n)**3
        assert tausum <= d8sum <= n*ht**7
        counts['divisor_moment_prefix_cases'] += 1
    for e in range(201):
        assert (e+1)**3 <= comb(e+7,7)
        counts['local_divisor_cases'] += 1
    for b in range(1,41):
        hb=harmonic(b)
        cop=sum((F(1,a*d) for a in range(1,b+1) for d in range(1,b+1) if gcd(a,d)==1),F(0))
        assert hb*hb <= 2*cop
        for k in (1,2,5,b+1):
            rays=sum((F(1,a*d) for a in range(k,b+1) for d in range(a+1,b+1) if gcd(a,d)==1),F(0))
            assert hb*hb/4-F(1,2)-harmonic(k-1)*hb <= rays
            counts['ray_mass_cases'] += 1
    for c in (2,3,4,12,35):
        for u in (2*c,2*c+1,4*c):
            tsum=sum(tau(c*m-1) for m in range(u,2*u))
            assert tsum <= 2*u*(harmonic(u)+1)
            counts['delayed_divisor_block_cases'] += 1
        for lo,hi in ((1,10),(3,25),(11,45)):
            g=sum((F(gcd(c*m-1,c*n-1),(c*m-1)*(c*n-1))
                for m in range(lo,hi+1) for n in range(m+1,hi+1)),F(0))
            wt=sum((F(tau(c*m-1),c*m-1) for m in range(lo,hi+1)),F(0))
            assert g <= harmonic(hi)*wt/c
            counts['full_gcd_kernel_cases'] += 1
    for _ in range(5000):
        a,b,c,e,u,v = [rng.randrange(1,41) for _ in range(6)]
        q,qq=12*a*b*u-1,12*c*e*v-1
        s,ss=3*a*a*u,3*c*c*v
        determinant=a*e-c*b
        assert 4*b*e*(s-ss)==a*e*q-c*b*qq+determinant
        assert (4*b*e)*(36*a*c*u*v)-1==q*qq+q+qq
        g=gcd(q,qq)
        assert ((s-ss)%g==0)==(determinant%g==0)
        counts['full_modulus_determinant_cases'] += 1
    # Auxiliary-cutoff decoder checks: not samples from the asymptotic actual-cutoff regime.
    seen = set()
    for a in range(1,5):
        for b in range(a+1,7):
            if gcd(a,b)!=1: continue
            for u in range(1,5):
                m,s=3*a*b*u,3*a*a*u; q=4*m-1
                n=(-4*s)%q
                while n <= q: n += q
                for _ in range(1000):
                    fn = factor(n)
                    if len(fn)==1 and next(iter(fn.values()))==1:
                        break
                    n += q
                else:
                    raise AssertionError('No prime decoder test input found in finite search')
                x=(n*m+s)//q; y=n*m; z=n*(m*x//s)
                assert (n*m+s)%q==0 and (m*x)%s==0
                assert 0<x<y<z and x<n
                assert F(4,n)==F(1,x)+F(1,y)+F(1,z)
                assert y%n==0 and z%n==0
                key=(n,x,y,z)
                assert key not in seen; seen.add(key)
                assert (y//n,q*x-n*m)==(m,s)
                if len(factor(n))==1 and next(iter(factor(n).values()))==1:
                    assert gcd(n,x)==1
                    counts['prime_type_ii_decoder_cases'] += 1
                counts['strict_decoder_cases'] += 1
    return {
        'status':'PASSED_FINITE_REGRESSION_ONLY',
        'seed':20260906,
        'counts':dict(sorted(counts.items())),
        'total_cases':sum(counts.values()),
        'elapsed_seconds':round(perf_counter()-started,3),
        'arithmetic':'Exact integers and fractions; no floating-point inequality checks.',
        'lean_executed':False,
        'asymptotic_claims_tested':False,
        'actual_eventual_rough_packet_regime_sampled':False,
        'limitations':'Finite Python checks do not establish theorem correctness or Lean elaboration.'
    }

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--json',type=Path)
    args=parser.parse_args()
    result=run()
    if args.json:
        args.json.parent.mkdir(parents=True,exist_ok=True)
        args.json.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
