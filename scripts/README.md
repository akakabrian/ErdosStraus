# Scripts

This directory will contain exact-arithmetic computational research code.

## Required profiler behavior

For each tested prime `p ≡ 1 mod 24`, search Type-II offsets and emit independently checkable certificates. Do not use floating-point equality.

Minimum successful-row schema:

```text
p
x
k
d = 4x-p
a
b
c
s
q (when applicable)
factorization(x)
factorization(d)
a_is_one
selected residue classes
```

Every emitted certificate must verify exactly:

```text
p+d = 4abc
a+b = ds
4xyz = p(xy+xz+yz)
1 ≤ x < y < z
```

with the corresponding denominator definitions.

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
