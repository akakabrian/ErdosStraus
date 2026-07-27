# Affine Type-II congruence sieve

## Purpose

This note records a finite exact sieve generated directly from the Type-II
factor-pair identity

```text
p + d = 4abc,
a + b = ds,
```

with `a < b < ps`. It is a congruence-reduction tool, not a proof of universal
coverage.

## Template C: fixed pair, affine `c`

Fix coprime positive integers `a < b` and choose `d ≡ 3 mod 4` with
`d | a+b`. Put

```text
s = (a+b)/d.
```

Whenever

```text
p ≡ -d mod 4ab,
```

write `c=(p+d)/(4ab)`. The Type-II identity then gives a strict decomposition
provided `c>0` and `b<ps`. The script checks these inequalities in the first
member of each progression; they then persist as the parameter grows.

## Template B: fixed `a,c`, affine `b`

Fix positive `a,c,d`, with `d ≡ 3 mod 4`, and impose

```text
p ≡ -(4a²c+d) mod 4acd.
```

Then

```text
b = (p+d)/(4ac)
```

is congruent to `-a mod d`, so `s=(a+b)/d` is integral. Again the script checks
`a<b<ps` at the first progression member. This template contains the modulo-11
families whose second factor grows with the progression parameter.

## Exact modulo-9240 reproduction

Command:

```bash
python scripts/affine_typeii_sieve.py \
  --modulus 9240 \
  --json data/affine-sieve-9240.json
```

Among the 240 unit residues modulo 9240 congruent to 1 modulo 24, the two
templates leave exactly the corrected 34 Ionascu–Wilson classes:

```text
1, 169, 289, 361, 529, 841, 961, 1369, 1681, 1849,
2041, 2209, 2521, 2641, 2689, 2809, 3361, 3481, 3529,
3721, 4321, 4489, 5041, 5161, 5329, 5569, 6169, 6241,
6889, 7561, 7681, 7921, 8089, 8761.
```

This independently reconstructs the formal modulo-9240 target from the general
Type-II architecture rather than from a hard-coded residue list.

## Larger finite sieves

Strict-safe enumeration gave:

| Modulus | Added factors | Unit population | Residual | Density |
|---:|---|---:|---:|---:|
| 9,240 | — | 240 | 34 | 14.1667% |
| 120,120 | 13 | 2,880 | 210 | 7.2917% |
| 2,042,040 | 13·17 | 46,080 | 1,849 | 4.0126% |
| 2,282,280 | 13·19 | 51,840 | 2,103 | 4.0567% |
| 38,798,760 | 13·17·19 | 829,440 | 17,512 | 2.1113% |

Thus these affine families continue to reduce density, but they do not yield a
finite universal cover in the tested moduli. The growing absolute residual set
is evidence that merely multiplying the modulus is not, by itself, a final
proof strategy.

## Integrity

- All enumeration uses integer divisibility and gcd checks.
- Every emitted family is checked at its first progression member for the
  strict inequalities required by the Formal Conjectures target.
- No finite residual count is interpreted as a statement about all primes.
- A claimed finite covering proof would still need each general family and the
  final finite residue cover kernel checked in Lean.
