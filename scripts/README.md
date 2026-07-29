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

## `consecutive_gate_profiler.py`

Profiles the full consecutive sequence

```text
m=(p+3)/4,
x_k=m+k,
d_k=4k+3.
```

For each bounded offset it compares the existing Type-II search with the complete factorization

```text
(d*y-p*x)(d*z-p*x)=p²*x².
```

It classifies the exponent of `p` in the smaller factor, normalizes exponent-zero hits to Type-I factor pairs, verifies every strict certificate by exact cross multiplication, and separately scans the unbounded unit Type-I gate supplied by prime divisors `d≡3 mod4` of `p+1`.

```bash
python scripts/consecutive_gate_profiler.py \
  --limit 100000000 \
  --max-k 40 \
  --json data/consecutive-offset-summary-100m.json
```

The `--max-k` bound applies only to the comparison of first bounded witnesses. The `p+1` divisor gate searches the complete factorization of `p+1` and may emit much larger offsets.

## `simultaneous_failure_profiler.py`

Restricts to residual primes for which the global unit Type-I gate fails, meaning `p+1` has no odd prime divisor congruent to `3 mod4`. It then records the first complete two-fraction witness in the bounded consecutive sequence.

```bash
python scripts/simultaneous_failure_profiler.py \
  --limit 100000000 \
  --max-k 40 \
  --json data/simultaneous-failure-summary-100m.json
```

This is an adversarial test of claims that adjoining the `p+1` gate forces a short offset bound. The committed run falsifies bounds `k≤10` and `k≤25`; it does not promote the observed `k≤26` ceiling to a theorem.

## `fixed_gate_automaton.py`

Implements the exact coprime-divisor gate for one odd modulus. For each prime power `q^e || x`, it may assign no power or one exponent `q^j`, `1≤j≤e`, to exactly one side. Either resulting divisor may equal `1`.

The implementation cross-checks its decision against direct divisor enumeration for a supplied finite input.

## `d11_component_automaton.py`

The name is retained for provenance, but the script now uses the exact prime-power-exponent semantics from `fixed_gate_automaton.py`. It also contains the former full-component model as a labeled legacy under-approximation so false negatives can be reproduced.

```bash
python scripts/d11_component_automaton.py \
  --audit-limit 10000000 \
  --json data/d11-legacy-audit-10m.json
```

Do not use the legacy model as an exact obstruction classifier.

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
