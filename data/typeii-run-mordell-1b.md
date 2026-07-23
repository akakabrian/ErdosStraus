# Exact Mordell-residue Type-II profile through 1,000,000,000

Date: 2026-07-22 (Pacific/Honolulu)

## Scope

This is finite exact computation over every prime `p ≤ 1,000,000,000` in the six classical Mordell residue classes:

```text
p mod 840 ∈ {1,121,169,289,361,529}.
```

It does not prove universal Type-II coverage or the Erdős–Straus conjecture. It does decisively falsify the earlier empirical hypotheses `k ≤ 26` and `d ≤ 107`.

## Programs

- `scripts/typeii_profiler.py` supplied exact results through `10^8`.
- `scripts/typeii_segmented_profiler.py` extended the Mordell-residue population from `10^8` through `10^9` with a segmented sieve.

Representative extension command:

```bash
python scripts/typeii_segmented_profiler.py \
  --start 100000001 \
  --limit 250000000 \
  --max-k 80 \
  --chunk-size 5000000 \
  --json chunk-100-250m.json
```

Six adjacent chunks covered `(10^8,10^9]`.

## Environment

```text
Python 3.13.5
Linux x86_64, kernel 6.12.13
5 visible CPU cores
CPU model: AMD EPYC 9V74
```

## Exact result

```text
Mordell-residue primes checked through 10^8:       179,468
Segmented extension primes in (10^8,10^9]:       1,408,113
Total primes checked:                             1,587,581
Unresolved with k ≤ 80:                                   0
Largest first-witness k:                                 31
Largest d=4k+3:                                         127
```

The six segmented chunks consumed 115.994814259 seconds of profiler search time in total.

## First-witness distribution

```text
k=0:   779,745
k=1:   386,431
k=2:   281,600
k=3:    61,701
k=4:    38,357
k=5:    26,567
k=6:     3,116
k=7:     6,532
k=8:       983
k=9:     1,311
k=10:      241
k=11:      610
k=12:       79
k=13:       95
k=14:      109
k=15:       28
k=16:        7
k=17:       39
k=18:        3
k=19:       13
k=20:        3
k=21:        5
k=22:        2
k=24:        1
k=25:        1
k=26:        1
k=31:        1
```

No first witnesses occurred at `k=23`, `27`, `28`, `29`, or `30` in this finite range.

## New record certificate

```text
p = 153,633,769
p mod 840 = 289
x = 38,408,474
k = 31
d = 127
q = 2,821,949

a = 113
b = 1,538
c = 221
s = 13

x = 2 * 13 * 17 * 113 * 769
```

Exact relations:

```text
p+d = 153,633,896 = 4x
q ∣ x²
q < x
d ∣ q+x
gcd(a,b)=1
x=abc
a+b=1,651=127*13=ds
a<b<ps
```

Strict denominators:

```text
X = abc  = 38,408,474
Y = pacs = 49,877,049,472,081
Z = pbcs = 678,857,540,602,306
```

They satisfy exactly:

```text
1 ≤ X < Y < Z
4XYZ = p(XY+XZ+YZ)
4/p = 1/X + 1/Y + 1/Z
```

The rational equality was checked with exact fractions; the difference is zero.

## Consequence

The earlier `p≤10^8` observation was not a universal bound:

```text
k ≤ 26     false as a universal empirical hypothesis
d ≤ 107    false as a universal empirical hypothesis
```

This is useful negative information. It prevents the proof program from hard-coding a false finite-offset ceiling.

## SHA-256

```text
scripts/typeii_segmented_profiler.py    6490ceac1d47e981addef01b516dddb85a4138319c93ea6093672d77f65117b5
data/typeii-summary-mordell-1b.json     cf132df8399aec68e336d4f3e7249e5bf93454f4c998bbe8b81e9fffcf44cb58
```
