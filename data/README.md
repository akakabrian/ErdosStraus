# Data

Store compact, reproducible summaries and checksums here. Avoid committing enormous raw datasets without compression or Git LFS planning.

## Reported finite experiment awaiting reproduction

The handoff reports an exact Type-II profile for primes:

```text
p ≤ 100,000,000
p ≡ 1 mod 24
```

Summary:

```text
primes_checked: 719781
unresolved: 0
largest_first_witness_k: 26
largest_d: 107
a_equals_one: 669859
nontrivial_a: 49922
```

Hardest reported case:

```text
p = 8803369
x = 2200869
d = 107
q = 121
a = 1
b = 18189
c = 121
s = 170
```

Reported denominators:

```text
2200869
181085300330
3293760527702370
```

These values are currently provenance notes, not a reproduced dataset. Before promoting them to verified project data, commit the generating script, exact command, output summary, and cryptographic checksums.

## Suggested files

```text
typeii-summary-1e8.json
record-holders.csv
coverage-by-offset.csv
checksums.txt
```

Every data file must state whether it is raw output, independently verified output, or a derived summary.
