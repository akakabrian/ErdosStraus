# Exact Type-II profile through 100,000,000

Date: 2026-07-22 (Pacific/Honolulu)

## Scope

Finite exact computation only. This run does not prove a universal bound on `k` or `d`, does not prove universal Type-II coverage, and does not prove the Erdős–Straus conjecture.

## Command

```bash
/usr/bin/time -v python scripts/typeii_profiler.py \
  --limit 100000000 \
  --max-k 26 \
  --json data/typeii-summary-100m.json
```

## Environment

```text
Python 3.13.5
Linux x86_64, kernel 6.12.13
5 visible CPU cores
CPU model: AMD EPYC 9V74
```

## Resource use

```text
wall time: 26.34 seconds
profiler search time: 25.219433913999865 seconds
maximum resident set size: 545,520 KiB
exit status: 0
```

## Exact result

```text
Primes checked:                         719,781
Resolved:                               719,781
Unresolved:                             0
Largest first-witness offset k:         26
Largest d = 4k+3:                       107
Witnesses using a=1:                    669,859
Witnesses needing nontrivial a:          49,922
```

Cumulative coverage:

```text
k ≤ 0:   430,409 / 719,781 = 59.79721609767415%
k ≤ 1:   665,555 / 719,781 = 92.46631961666118%
k ≤ 2:   700,591 / 719,781 = 97.33391128690532%
k ≤ 5:   717,690 / 719,781 = 99.70949497138713%
k ≤ 10:  719,589 / 719,781 = 99.97332521975434%
k ≤ 15:  719,771 / 719,781 = 99.99861068852887%
k ≤ 26:  719,781 / 719,781 = 100% of this finite range
```

Record witness:

```text
p = 8,803,369
x = 2,200,869
k = 26
d = 107
q = 121
a = 1
b = 18,189
c = 121
s = 170
x = 3^2 * 11^2 * 43 * 47
```

## Exact checks performed per witness

The profiler rejects a candidate unless all of the following integer conditions hold:

```text
p+d = 4x
q ∣ x²
q < x
d ∣ q+x
gcd(a,b)=1
x=abc
a+b=ds
a<b<ps
1 ≤ abc < pacs < pbcs
4XYZ = p(XY+XZ+YZ)
```

No floating-point arithmetic is used for certificate verification.

## SHA-256

```text
scripts/typeii_profiler.py    f371cb870087fcf1bae9b75f0421ebce68a99f964c3a205933be4e0992e69b1b
data/typeii-summary-100m.json 6b2308e297ac48e2e598b2fff1c7184f5dcb11f9b66264715c17461ba096252b
```
