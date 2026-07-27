# Scripts

Exact-arithmetic computational research code for Erdős–Straus / Erdős Problem 242.

## `typeii_profiler.py`

Searches residual primes `p ≡ 1 mod 24`. For

```text
x = (p+3)/4 + k,
d = 4k+3,
```

it enumerates divisors `q ∣ x²` with `q < x` and `d ∣ q+x`, normalizes them to coprime factor-pair parameters, and rejects any candidate that fails an exact strict certificate check.

Example:

```bash
python scripts/typeii_profiler.py \
  --limit 100000000 \
  --max-k 26 \
  --csv data/typeii-100m.csv \
  --json data/typeii-summary-100m.json
```

The CSV is optional. The 100-million run produces 719,781 successful rows and is intentionally regenerated rather than committed uncompressed.

Successful-row schema:

```text
p
x
k
d = 4x-p
q
a
b
c
s
a_is_one
factorization(x)
factorization(d)
```

Every emitted certificate verifies exactly:

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

No floating-point arithmetic is used.

## `typeii_segmented_profiler.py`

Uses a segmented sieve to scan large intervals of primes in Mordell's six classes modulo 840 without allocating a full-range prime table.

```bash
python scripts/typeii_segmented_profiler.py \
  --start 100000001 \
  --limit 1000000000 \
  --max-k 80 \
  --json data/typeii-summary-mordell-1b.json
```

This script found the exact record `p=153633769`, `k=31`, disproving the earlier empirical ceiling `k≤26` while leaving the universal conjecture open.

## `affine_typeii_sieve.py`

Enumerates two strict-safe affine specializations of the Type-II factor-pair identity:

- fixed `a,b`, affine `c`;
- fixed `a,c`, affine `b`.

It reports unit residues `r ≡ 1 mod 24` not covered by those congruence families. At modulus 9240 it reconstructs exactly the corrected 34 residual classes.

```bash
python scripts/affine_typeii_sieve.py \
  --modulus 9240 \
  --json data/affine-sieve-9240.json
```

The output is a finite congruence sieve. A nonzero residual set is not a counterexample, and a zero residual set would still require the general families and final cover to be kernel checked.

## `verify_certificate.py`

Checks one JSON factor-pair certificate with exact integers and `fractions.Fraction`:

```bash
python scripts/verify_certificate.py data/record-holder-8803369.json
```

## Reproducibility requirements

Each run should record:

- source commit;
- language/runtime version;
- command line and parameters;
- range and prime-generation method;
- row counts and unresolved cases;
- elapsed time and hardware summary;
- output checksums.

## Integrity

A finite successful run is evidence only. Scripts must never print or encode a claim that the universal conjecture is proved.
