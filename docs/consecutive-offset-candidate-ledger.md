# Consecutive-offset candidate ledger

This ledger applies the project acceptance protocol to the global sequence

```text
m=(p+3)/4,
x_k=m+k,
d_k=4k+3
```

for a hypothetical residual prime `p≡1 mod24`. A candidate is not promoted by
finite coverage alone.

## C1 — Complete factorization after fixing `x_k`

### Precise statement

Let `p,x,d,y,z` be positive integers with `p+d=4x`. Then

```text
4/p = 1/x + 1/y + 1/z
```

is equivalent to

```text
(dy-px)(dz-px)=p²x².
```

For a strict solution with `x<y<z` and `0<d<p`, the factors

```text
u=dy-px,
v=dz-px
```

satisfy

```text
0<u<px<v,
u*v=p²x²,
u≡-px (mod d).
```

### Falsification attempt

Expanded both sides symbolically and checked all emitted finite witnesses by
exact cross multiplication. No counterexample exists because this is an
algebraic equivalence.

### Status

**PROVEN algebraically.** The current Lean work formalizes the exponent-zero
Type-I specialization; a reusable Lean theorem for the complete factorization
itself remains to be added.

### Deductive edge

Because `p` is prime and `gcd(p,x)=1`, the exponent of `p` in the smaller
factor is `0`, `1`, or `2`. This proves that the fixed Type-II architecture is
only the middle branch of the complete search space.

## C2 — Strict Type-I factor-pair certificate

### Precise statement

Let `p,a,b,c,s,d` be positive natural numbers satisfying

```text
p+d=4abc,
a+p*b=d*s.
```

If

```text
b<s,
a<p*b,
```

then

```text
X=abc,
Y=acs,
Z=p*b*c*s
```

satisfy

```text
1≤X<Y<Z,
4XYZ=p(XY+XZ+YZ).
```

Moreover, `0<d<p` implies `b<s`, so under the offset inequality only
`a<p*b` remains as a separate strictness condition.

### Falsification attempt

The identity was independently expanded and every Type-I witness emitted
through `p≤10^8` was checked by exact integer arithmetic. No violation was
found. The proof itself is symbolic and does not depend on the finite run.

### Status

**PROVEN and formalized** on formal branch
`agent/erdos-242-consecutive-offsets` in `TypeIFactorPair.lean`. Acceptance as
kernel-audited project infrastructure is pending the branch CI result.

### Deductive edge

This supplies the missing exponent-zero branch of the complete factorization
and produces decompositions strictly earlier than the first Type-II witness
for 1,590 residual primes in the finite `10^8` profile.

## C3 — Unit Type-I gate across the complete offset sequence

### Precise statement

Assume

```text
p+3=4m,
d_k=4k+3,
x_k=m+k.
```

Then `p+d_k=4x_k`. If

```text
d_k<p,
d_k | p+1,
```

and `s=(p+1)/d_k`, then

```text
4/p = 1/x_k + 1/(x_k*s) + 1/(p*x_k*s)
```

with strict denominator order.

For a prime `p≡1 mod24`, any odd prime divisor `r|p+1` with `r≡3 mod4`
meets these hypotheses. Hence failure of this gate for a hypothetical prime
counterexample forces every odd prime divisor of `p+1` to be `1 mod4`.

### Falsification attempt

Factored `p+1` for every one of the 719,781 residual primes through `10^8`,
constructed every selected certificate with exact integers, and checked the
strict polynomial identity. The largest selected offset was `k=1760`, showing
that this is not a disguised small fixed gate.

### Status

**PROVEN and formalized** in `ConsecutiveOffsets.lean`; kernel-audit acceptance
is pending current CI.

### Deductive edge

This is the first new complete-sequence mechanism in the project that converts
prolonged failure into a splitting restriction on an adjacent global integer,
`p+1`.

## C4 — Every residual prime has a unit Type-I gate

### Precise candidate

```text
For every prime p≡1 mod24, p+1 has an odd prime divisor r≡3 mod4.
```

### Counterexample

```text
p=73,
p+1=74=2*37,
37≡1 mod4.
```

### Status

**FALSIFIED.** The unit gate is a rigorous infinite family, not universal
coverage.

### Deductive edge retained

Its failure still proves that the odd part of `p+1` is composed entirely of
primes `1 mod4`.

## C5 — Unit gate or a bounded complete offset

### Precise candidates

For a fixed `B`, define:

```text
C(B): every residual prime p either has the unit p+1 gate
      or has a complete two-fraction witness at some k≤B.
```

### Counterexamples

`C(10)` is false:

```text
p=496609,
p+1=2*5*53*937,
all odd factors are 1 mod4,
first complete witness k=12.
```

`C(25)` is false:

```text
p=8803369,
p+1=2*5*880337,
all odd factors are 1 mod4,
first complete witness k=26.
```

### Status

**FALSIFIED for `B=10` and `B=25`.** The finite `10^8` run has no unresolved
case for `B=26`, but that is computation only and is not promoted to a
universal claim.

### Deductive edge

These counterexamples rule out the simplest proposed contradiction from a
short initial block of gates, even after adjoining the global `p+1` family.
Any bounded-gate theorem needs a new argument rather than an empirical ceiling.

## C6 — Type-I is redundant with the first Type-II offset

### Precise candidate

```text
For every residual prime p, the first complete two-fraction witness occurs at
the same offset as the first Type-II witness.
```

### Counterexample

```text
p=386401,
p+1=2*193201,
exact Type-II gates at k=0,1,2 fail,
first complete witness k=2 is Type-I:
  a=3, b=2477, c=13, s=87010480.
The first Type-II witness occurs at k=13.
```

### Status

**FALSIFIED.** Type-I is a genuinely additional structural branch.

### Deductive edge

This validates re-evaluating the Type-II-only architecture rather than merely
adding more fixed Type-II gates.

## C7 — Entire prime-power components give the exact `d=11` gate

### Precise candidate

```text
For x=product q_i^e_i, it is enough to assign each entire q_i^e_i to one
side, the other side, or neither, with both sides nonempty.
```

### Counterexamples

```text
x=1849=43^2:       (1,43) succeeds modulo 11;
p=4201, x_2=1053: (9,13) succeeds modulo 11.
```

The former model misses the divisor `1` and partial exponents such as
`3^2` from `3^4`.

### Status

**FALSIFIED.** Through `p≤10^7`, the legacy model missed 1,124 exact `d=11`
successes after exact failure of the first two gates.

### Deductive edge

All future local-global work must use arbitrary prime-power exponents and may
seek only a proved quotient of that exact state space.

## C8 — Combined splitting restrictions force a contradiction

### Precise current obligation

A hypothetical prime counterexample must simultaneously satisfy at least:

```text
all odd prime factors of p+1 are 1 mod4;
all prime factors of (p+3)/4 are 1 mod3;
all prime factors of (p+7)/4 are quadratic residues mod7;
and every later exact Type-I/Type-II gate fails.
```

The candidate global theorem is that this infinite system is inconsistent, or
that sufficiently prolonged failure produces a strictly smaller object with
the same counterexample property.

### Falsification attempt

Finite residual primes can satisfy the first several listed restrictions, so
no contradiction follows from the first two or three local conditions alone.
The examples `p=386401`, `p=496609`, and `p=8803369` defeat progressively
stronger short-block versions.

### Status

**OPEN/BLOCKED.** No monotone descent parameter or local-global incompatibility
has yet been proved.

### Deductive edge

This is narrower than the old `ResidualPrimeCoverage` placeholder: it exposes
the exact simultaneous multiplicative-splitting system that a successful
global mechanism must contradict.
