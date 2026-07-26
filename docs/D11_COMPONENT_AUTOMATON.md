# Exact d=11 Prime-Power Component Automaton

## Scope

This note studies only the normalized `d=11` Type-II gate. It does not prove
universal Erdős–Straus coverage.

For

```text
x = product q_i^e_i,
```

coprime divisors `a,b | x` are obtained by assigning each full prime-power
component `q_i^e_i` to `a`, to `b`, or to neither. Splitting one component
between both sides would violate coprimality. Therefore the finite-state search
on component residues modulo 11 is exact.

A state is

```text
(a mod 11, b mod 11, a_nonempty, b_nonempty).
```

For each component residue `r`, the transition assigns `r` to the left side,
the right side, or neither. The gate succeeds exactly when a reachable state
has both sides nonempty and

```text
a + b = 0 mod 11.
```

## Dataset result through 10^8

Input population:

```text
719,781 primes p <= 100,000,000 with p = 1 mod 24.
```

Only 19,190 rows have first Type-II witness index `k >= 3`, so they survive the
`d=3`, `d=7`, and `d=11` checks. For every one of these rows, the exact
automaton applied to

```text
x11 = (p + 11) / 4
```

returns failure, as it must if the profiler and automaton agree.

This is an independent consistency check of the gate semantics; it is not a
finite proof of the conjecture.

## Minimal forcing patterns

The pairwise patterns are exactly the additive opposites:

```text
(1,10), (2,9), (3,8), (4,7), (5,6).
```

There are additional genuinely multiplicative three-component patterns. Among
the simplest are:

```text
(1,2,5)
(2,3,3)
(2,3,4)
(2,3,5)
(3,4,6)
(3,6,9)
(4,4,6)
(5,5,8)
```

For example, `(2,3,3)` succeeds even though no two listed residues are additive
opposites: assigning `2*3 = 6` to one side and `3` to the other gives
`6 + 3 != 0`, but a different disjoint assignment in the exact state graph
produces the required opposite products. The script is the authoritative way
to recover the witness state; hand inspection of support alone is unsafe.

## Structural split for residual primes

For a residual prime `p = 1 mod 24`, `x11=(p+11)/4` is divisible by 3.
The formal branch now contains explicit trigger theorems for prime divisors
congruent to `7`, `8`, or `10 mod 11`.

The quadratic-residue subgroup

```text
H = {1,3,4,5,9}
```

is multiplicatively closed and contains no additive opposite pair. Hence if
every prime factor of `x11` lies in `H`, the `d=11` gate fails.

The exact automaton shows that the unresolved region is not described merely by
prime support. Prime-power exponents change component residues, and mixed
signatures involving residues `2` and `6` can either trigger or fail depending
on the full multiset.

## Next theorem target

The useful next target is not a fixed bound on the number of prime factors. It
is a finite classification of minimal failing component multisets compatible
simultaneously with:

1. failure of the exact `d=3` gate;
2. failure of the exact `d=7` gate;
3. `p` lying in one of the 34 modulo-9240 residual classes;
4. the affine relation `4*x11 = p+11`.

Any claimed classification must be proved exhaustive. Dataset enumeration is
only a falsification and discovery tool.
