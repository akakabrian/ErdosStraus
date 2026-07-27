# Formal Foundation: Mathematical Audit

## Certificate equivalence

For positive natural numbers `n,x,y,z`, the rational equation

```text
4/n = 1/x + 1/y + 1/z
```

is equivalent to

```text
4xyz = n(xy + xz + yz).
```

The Lean library takes the polynomial identity as the certificate and carries positivity and strict-order hypotheses separately.

## Strict elementary families

### Even `n = 2m`, `m ≥ 2`

```text
x = m
y = m+1
z = m(m+1)
```

The strict inequalities follow from `m ≥ 2` and `m+1 < m(m+1)`.

### `n = 3k+2`, `k ≥ 1`

```text
x = k+1
y = 3k+2
z = (3k+2)(k+1)
```

### `n = 4k+3`

Let `M = (4k+3)(k+1)`:

```text
x = k+1
y = M+1
z = M(M+1)
```

### `n = 8k+5`

```text
x = 2(k+1)
y = (8k+5)(k+1)
z = 2(8k+5)(k+1)
```

All four families are formulated directly as strict polynomial certificates.

## Scaling

A strict certificate for `n` scales to one for `mn` by replacing:

```text
(x,y,z) ↦ (mx,my,mz)
```

for `m>0`. Strict order is preserved because multiplication by a positive natural is strictly monotone.

## Residue reduction

For `n>2`, all residues modulo 24 except 1 fall into at least one of:

```text
n ≡ 0 mod 2
n ≡ 0 mod 3
n ≡ 2 mod 3
n ≡ 3 mod 4
n ≡ 5 mod 8.
```

The `0 mod 3` case scales the strict decomposition of 3. Therefore any strict counterexample must satisfy:

```text
n ≡ 1 mod 24.
```

## Least-counterexample primality

Assume a counterexample exists and choose the least one `p`. If `p = ab` with both factors proper and positive, the proof aims to show `a>2`, invoke minimality to obtain a strict decomposition of `a`, and scale by `b`, contradicting that `p` is a counterexample. Combined with residue reduction, this yields a prime counterexample `p ≡ 1 mod 24` if any counterexample exists.

This theorem remains conditional: it reduces the universal problem but does not prove there is no such prime.

## Type-II factor-pair certificate

Given positive parameters satisfying:

```text
p+d = 4abc
a+b = ds,
```

the denominators

```text
abc,
pacs,
pbcs
```

satisfy the polynomial Erdős–Straus identity. Additional hypotheses `a<b<ps` establish strict order.

## Opposite coprime divisors

If `a,b` are coprime divisors of `x`, then `ab ∣ x`. Writing `x=abc` and assuming `d ∣ a+b` supplies `s` with `a+b=ds`. If also `p+d=4x` and `d<p`, the Type-II strict certificate follows.

## First gate `d=3`

A divisor `q ∣ x` with `q ≡ 2 mod 3` pairs with `1`:

```text
gcd(1,q)=1,
3 ∣ 1+q.
```

Thus, for `p+3=4x`, this is a sufficient `d=3` Type-II gate. A later research step must precisely characterize when such a divisor exists in terms of the prime factorization of `x`.
