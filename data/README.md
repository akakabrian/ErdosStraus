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

## Integrity

This is finite evidence only. It does not prove that `k ≤ 26` or `d ≤ 107` universally, that every prime admits a Type-II certificate, or that the Erdős–Straus conjecture is true.

Every future data file must state whether it is raw output, independently verified output, or a derived summary.
