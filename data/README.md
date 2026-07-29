# Data

Store compact, reproducible summaries and checksums here. Avoid committing enormous raw datasets without compression or Git LFS planning.

## Reproduced finite experiment

The exact Type-II profile was independently reproduced for primes:

```text
p ≤ 100,000,000
p ≡ 1 mod 24
```

using `scripts/typeii_profiler.py` and exact integer verification.

Result:

```text
primes_checked: 719781
resolved: 719781
unresolved: 0
largest_first_witness_k: 26
largest_d: 107
a_equals_one: 669859
nontrivial_a: 49922
```

Record case:

```text
p = 8803369
x = 2200869
k = 26
d = 107
q = 121
a = 1
b = 18189
c = 121
s = 170
```

Strict denominators:

```text
2200869
181085300330
3293760527702370
```

Files:

```text
typeii-summary-100m.json  compact machine-readable result
typeii-run-100m.md        command, environment, exact checks, percentages, hashes
record-holder-8803369.json single-certificate fixture
```

The complete successful-witness CSV contains 719,781 rows and was 44 MiB uncompressed. It was generated and analyzed locally but is intentionally not committed on this branch; the deterministic profiler can regenerate it with `--csv`.

Raw CSV SHA-256 from the reproduced run:

```text
399602d5b46526f2f8eb0505c80dbad25a13c2eec378e9ce84a8d6314c31ee0b
```

## Complete consecutive-offset profile through `10^8`

Command:

```bash
python scripts/consecutive_gate_profiler.py \
  --limit 100000000 \
  --max-k 40 \
  --json data/consecutive-offset-summary-100m.json
```

The script compares the Type-II-only search with the complete factorization of the two remaining unit fractions after fixing `x_k`, and independently scans the unbounded unit Type-I gate obtained from prime divisors `d≡3 mod4` of `p+1`.

Compact result:

```text
residual_primes_checked:                         719781
Type-II unresolved through k=40:                      0
complete factorization unresolved through k=40:       0
first witness strictly earlier than Type-II:        1590
largest observed offset improvement:                  15
unit Type-I p+1 gate covered:                     398283
unit Type-I p+1 gate not covered:                 321498
largest observed unit-gate k:                       1760
```

SHA-256:

```text
scripts/consecutive_gate_profiler.py
ff7ff97d3efb8551807e68922c67ccb9f7f49c924ebfafcbaf7eccf86866691e

data/consecutive-offset-summary-100m.json
51567149171af3317a4570cc87f6c7c296845c560f2fa4c911c812a266518400
```

The selected `p`-exponent counts in the JSON describe the least factor `u` chosen at the first successful offset. They do not assert that the corresponding prime has no certificate of another type at the same offset.

## Corrected `d=11` automaton audit through `10^7`

Command:

```bash
python scripts/d11_component_automaton.py \
  --audit-limit 10000000 \
  --json data/d11-legacy-audit-10m.json
```

After exact failure at `d=3` and `d=7`, 7,144 residual primes reached the `d=11` check. The exact prime-power-exponent automaton succeeded for 4,419; the former full-component model succeeded for only 3,295 and therefore missed 1,124 valid gates.

The committed JSON is a compact derived summary containing the counts, five representative false negatives, and two regression fixtures. The script prints a longer list of representative rows when rerun.

## Integrity

This is finite evidence only. It does not prove a universal bound on `k` or `d`, that every prime admits a Type-I or Type-II certificate, that the unit Type-I gate covers every prime, or that the Erdős–Straus conjecture is true.

Every future data file must state whether it is raw output, independently verified output, or a derived summary.
