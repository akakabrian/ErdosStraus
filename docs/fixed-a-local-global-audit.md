# Fixed-`a` local-global audit

## Scope

This note records accepted arithmetic consequences, exact falsification tests, and the current blocker for the fixed-`a` Type-I family. Finite sieves and numerical coverage are not universal proofs.

## Accepted strict gate

For positive natural numbers satisfying

```text
p+a=d*s,
p+d=4*a*c,
1≤a<p,
0<d<p,
```

the denominators

```text
X=a*c,
Y=a*c*s,
Z=p*c*s
```

obey

```text
1≤X<Y<Z,
4XYZ=p(XY+XZ+YZ).
```

This is formalized as

```text
ErdosStraus.fixedA_typeI_gate_hasDistinctDecomposition
```

in the Formal Conjectures branch `agent/erdos-242-consecutive-offsets`.

## First two additive-shift obstructions

### Shift `p+1`

For a residual target `p+3=4m`, every divisor `r|p+1` with

```text
r≡3 mod4
```

is an offset `r=4k+3` and opens the strict unit Type-I gate. Therefore a hypothetical counterexample has no divisor of `p+1` congruent to `3 mod4`.

Formal theorems:

```text
ErdosStraus.divisor_mod_four_three_hasDistinctDecomposition
ErdosStraus.counterexample_no_divisor_mod_four_three
```

### Shift `p+2`

For `p≡1 mod8`, every divisor `d|p+2` with

```text
d≡7 mod8
```

opens the strict fixed-`a` gate with `a=2`. Therefore a hypothetical counterexample congruent to `1 mod8` has no divisor of `p+2` congruent to `7 mod8`.

Formal theorems:

```text
ErdosStraus.divisor_mod_eight_seven_hasDistinctDecomposition
ErdosStraus.counterexample_no_divisor_mod_eight_seven
```

An elementary prime-factor corollary is that failure at `a=2` forces every prime divisor of `p+2` into residues `1` or `3 mod8`: a prime `7 mod8` is a direct gate, while a prime `5 mod8` has complementary divisor `7 mod8` because `p+2≡3 mod8`.

## Dynamic factorization versus affine families

The exact fixed-`a` condition factors the actual integer `p+a` and seeks a proper divisor

```text
d≡-p mod4a.
```

A finite affine specialization fixes `(a,d)` in advance. To test whether the strong finite coverage was merely another residue-class cover, `scripts/fixed_a_affine_sieve.py` enumerated all pairs with

```text
4a|9240,
d|9240,
d odd.
```

Among the 240 unit residues modulo `9240` congruent to `1 mod24`, these pairs cover 190 and leave 50. The residual classes are recorded in

```text
data/fixed-a-affine-sieve-9240.json.
```

The existing Type-II affine sieve leaves 34 classes. Every one of those 34 classes also survives the fixed-`a` affine sieve. Thus the fixed-`a` finite success is not explained by a stronger finite residue cover at modulus `9240`; it uses the target-dependent divisor structure of `p+a`.

## Exact finite evidence

The dynamic profiler found a fixed-`a` certificate for:

```text
all 719,781 residual primes p≤10^8 with a≤1000;
all 1,408,113 Mordell-residual primes 10^8<p≤10^9 with a≤2000.
```

The largest first parameter observed through these runs was

```text
p=5,101,441,
a=890,
d=39,
c=1,433,
s=130,829.
```

This is finite evidence only. No universal upper bound on `a` has been proved.

## Exact remaining obligation

A complete fixed-`a` proof would establish one of the following:

1. every residual prime admits some `1≤a<p` and proper divisor `d|p+a` with `d≡-p mod4a`;
2. sufficiently long simultaneous failure of these divisor conditions contradicts primality or the already-proved splitting conditions;
3. prolonged failure produces a strictly smaller target carrying the same counterexample property.

No such local-global theorem or descent is currently proved.
