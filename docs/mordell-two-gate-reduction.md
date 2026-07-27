# Mordell's modulo-840 reduction from the first two Type-II gates

## Status

This note gives an exact proof architecture for the classical six residual prime classes modulo 840 using only:

- the already formalized reduction to primes `p ≡ 1 (mod 24)`;
- divisor scaling for primes dividing 5 or 7;
- explicit factor-pair certificates with offsets `d=3` and `d=7`.

It is not a proof of the Erdős–Straus conjecture. It reduces the remaining prime problem from one class modulo 24 to six classes modulo 840.

## 1. Start from `p = 24k+1`

For a hypothetical prime counterexample after Phase 1, write

```text
p = 24k+1.
```

The first candidate denominator is

```text
x0 = (p+3)/4 = 6k+1,       d=3,
```

and the second is

```text
x1 = (p+7)/4 = 2(3k+1),    d=7.
```

## 2. Reduction modulo 120

Analyze `k mod 5`.

### `k ≡ 1 (mod 5)`

Then `5 ∣ p`. For prime `p`, this forces `p=5`, which is already solved by an elementary strict family.

### `k ≡ 3 (mod 5)`

Write `k=5t+3`, so

```text
p = 120t+73.
```

Use the Type-II factor-pair parameters

```text
a=2,
b=5,
c=3t+2,
s=1,
d=7.
```

They satisfy

```text
a+b = 7 = d*s,
p+d = 120t+80 = 4*2*5*(3t+2)=4abc.
```

The strict inequalities are immediate:

```text
0<a<b<p*s.
```

Thus every `p ≡ 73 (mod 120)` has a strict decomposition.

### `k ≡ 4 (mod 5)`

Write `k=5t+4`, so

```text
p = 120t+97.
```

Use

```text
a=1,
b=5,
c=6t+5,
s=2,
d=3.
```

Then

```text
a+b = 6 = d*s,
p+d = 120t+100 = 4*1*5*(6t+5)=4abc.
```

Therefore every `p ≡ 97 (mod 120)` has a strict decomposition.

### Surviving cases

Only `k ≡ 0,2 (mod 5)` remain, giving

```text
p ≡ 1 or 49 (mod 120).
```

## 3. Reduction modulo 168

Analyze `k mod 7`.

### `k ≡ 2 (mod 7)`

Then `7 ∣ p`. For prime `p`, this forces `p=7`, already covered by an elementary strict family.

### `k ≡ 3 (mod 7)`

Write `k=7t+3`, so

```text
p = 168t+73.
```

Use

```text
a=1,
b=42t+20,
c=1,
s=6t+3,
d=7.
```

Indeed,

```text
a+b = 42t+21 = 7(6t+3),
p+d = 168t+80 = 4(42t+20).
```

### `k ≡ 4 (mod 7)`

Write `k=7t+4`, so

```text
p = 168t+97.
```

Use

```text
a=1,
b=21t+13,
c=2,
s=3t+2,
d=7.
```

Then

```text
a+b = 21t+14 = 7(3t+2),
p+d = 168t+104 = 8(21t+13)=4abc.
```

### `k ≡ 6 (mod 7)`

Write `k=7t+6`, so

```text
p = 168t+145,
x1 = 42t+38 = 2(21t+19).
```

The divisor-square certificate with

```text
d=7,
q=4
```

satisfies

```text
q ∣ x1^2,
q+x1 = 42t+42 = 7(6t+6),
q<x1,
p+d=4x1.
```

For prime `p`, the formal theorem `prime_divisorSquare_hasDistinctDecomposition` discharges the needed coprimality automatically from `0<x1<p`.

Equivalently, this case can be split into two direct factor-pair families modulo 336:

```text
t=2u:
  p=336u+145,
  (a,b,c,s,d)=(2,42u+19,1,6u+3,7).

t=2u+1:
  p=336u+313,
  (a,b,c,s,d)=(1,21u+20,4,3u+3,7).
```

### Surviving cases

Only `k ≡ 0,1,5 (mod 7)` remain, giving

```text
p ≡ 1,25,121 (mod 168).
```

## 4. Chinese remainder intersection

Combine

```text
p ≡ 1 or 49       (mod 120)
```

with

```text
p ≡ 1,25,or 121   (mod 168).
```

Since `lcm(120,168)=840`, the intersection is exactly

```text
p ≡ 1,121,169,289,361,529 (mod 840).
```

These are the six classical Mordell residual classes.

## 5. Computational cross-check through 100 million

The independently reproduced exact Type-II profile has the following sharp finite behavior:

- every tested prime outside the six Mordell classes has first witness `k≤1`, hence `d≤7`;
- every tested prime with first witness `k>1` lies in one of the six classes;
- all ten tested primes with `k>15` lie in the six classes.

This computational observation is explained by the universal families above; it is not being used as proof.

## 6. Lean implementation plan

Create a new module, after the divisor-square normalization is stable, containing:

1. strict factor-pair families for `120t+73`, `120t+97`, `168t+73`, and `168t+97`;
2. either the divisor-square `168t+145` theorem or its two direct modulo-336 families;
3. the modulo-120 prime-counterexample reduction;
4. the modulo-168 prime-counterexample reduction;
5. the CRT combination to the six residues modulo 840;
6. an axiom and warnings-as-errors audit.

The final output should be a conditional theorem of the form:

```text
If a strict counterexample exists, then one exists at a prime
p ≡ 1,121,169,289,361,or 529 (mod 840).
```

The universal conjecture remains open after this reduction.
