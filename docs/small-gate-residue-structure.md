# Prime-factor residue structure of the first Type-II gates

## Status

This note separates exact elementary characterizations from finite cross-checks. The `d=3` and `d=7` statements below are universal arithmetic facts. The counts through `10^8` are finite evidence validating the profiler and showing how often simultaneous avoidance occurs.

## Setup

For a residual prime

```text
p ≡ 1 (mod 24),
```

write

```text
x_k = (p+3)/4 + k,
d_k = 4k+3.
```

The Type-II divisor-pair gate at offset `k` asks for coprime divisors `a,b ∣ x_k` satisfying

```text
a+b ≡ 0 (mod d_k).
```

The first candidates are:

```text
x_0=(p+3)/4,  d_0=3,
x_1=(p+7)/4,  d_1=7,
x_2=(p+11)/4, d_2=11.
```

## 1. Exact characterization of the `d=3` gate

Because `p ≡ 1 mod 24`, one has

```text
x_0 ≡ 1 (mod 3),
```

so `3 ∤ x_0`.

### Success from a nonresidue prime factor

If a prime `q ∣ x_0` satisfies

```text
q ≡ 2 (mod 3),
```

then the pair

```text
a=1,
b=q
```

is coprime, divides `x_0`, and has `a+b ≡ 0 mod 3`. This is already kernel checked in `SmallGates.lean`.

### Converse

Suppose every prime factor of `x_0` is `1 mod 3`. Every divisor of `x_0` is then a product of such prime powers, hence is also `1 mod 3`. For any two divisors `a,b`:

```text
a+b ≡ 1+1 ≡ 2 (mod 3),
```

so `3 ∤ a+b`. Therefore no opposite-divisor certificate exists.

Thus:

> The `d=3` gate succeeds exactly when `x_0` has a prime factor congruent to `2 mod 3`.

Equivalently, failure forces all prime factors of `x_0` to split in the quadratic-residue class modulo 3.

## 2. Exact characterization of the `d=7` gate

For `p ≡ 1 mod 24`:

```text
x_1=(p+7)/4
```

is even. For a prime target `p>7`, the offset equation implies `gcd(7,x_1)=1`, so all prime factors of `x_1` are units modulo 7.

The quadratic residues modulo 7 form the multiplicative subgroup

```text
H={1,2,4}.
```

Its negatives are exactly the nonresidues:

```text
-H={6,5,3}.
```

### Explicit success triggers

Let `q` be a prime divisor of the even number `x_1`.

- If `q ≡ 6 mod 7`, use `(a,b)=(1,q)`.
- If `q ≡ 5 mod 7`, use `(a,b)=(2,q)`.
- If `q ≡ 3 mod 7`, use `(a,b)=(1,2q)`.

The needed divisibilities and coprimalities follow because `2∣x_1`, `q∣x_1`, and an odd prime `q` is coprime to 2. These three constructions are formalized on the branch `erdos-242-small-gate-residues`.

### Converse

If every prime factor of `x_1` lies in `H`, then every divisor of `x_1` lies in `H` because `H` is multiplicatively closed. If divisors `a,b` satisfied `a+b≡0 mod7`, then `b≡-a`, forcing one residue into `H` and the other into `-H`. The two sets are disjoint, a contradiction.

Thus:

> For even `x_1` coprime to 7, the `d=7` gate succeeds exactly when `x_1` has a prime factor in `{3,5,6} mod 7`.

Equivalently, failure forces every prime factor of `x_1` to be a quadratic residue modulo 7.

## 3. A necessary prime-factor condition for failure at `d=11`

Here

```text
x_2=(p+11)/4
```

is divisible by 3. The fixed divisors `1` and `3` give immediate triggers:

- `q ≡ 10 mod 11`: pair `(1,q)`;
- `q ≡ 8 mod 11`: pair `(3,q)`;
- `q ≡ 7 mod 11`: pair `(1,3q)`.

Therefore failure of the `d=11` gate implies that no prime factor of `x_2` lies in

```text
{7,8,10} (mod 11).
```

This is only a necessary condition. Composite products of other prime residues can also create opposite divisors, so avoiding these three prime classes is not by itself sufficient for failure.

## 4. Exact finite cross-check through `10^8`

The committed exact profiler data was re-analyzed by factoring the relevant earlier candidate values, not merely the eventual witness value.

```text
Primes whose first witness has k>0: 289,372
Violations of the d=3 characterization: 0

Primes whose first witness has k>1:  54,226
Violations of the d=7 characterization: 0
Observed prime-factor residues in x_1: {1,2,4} mod 7

Primes whose first witness has k>2:  19,190
Prime factors of x_2 in {7,8,10} mod 11: 0
Observed residues in x_2: {1,2,3,4,5,6,9} mod 11
```

These zero-violation counts are expected consequences of the exact trigger lemmas; they are useful as an independent consistency check on the search implementation.

## 5. Research direction

The first two failures impose simultaneous splitting restrictions on two nearby linear forms:

```text
all prime factors of (p+3)/4 are 1 mod 3,
all prime factors of (p+7)/4 are in {1,2,4} mod 7.
```

Later gate failures impose related avoidance conditions on further shifted values. A possible universal proof would need to show that a prime `p` cannot satisfy the entire growing system indefinitely, or that one of the later composite-divisor interactions must eventually produce an opposite pair.

This reframes the main problem as simultaneous multiplicative-subgroup avoidance across a sequence of shifted integers rather than as a bounded-offset search.
