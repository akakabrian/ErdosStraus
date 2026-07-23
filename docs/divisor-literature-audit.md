# Divisor-Certificate Literature Audit

## Scope

This note extracts reusable exact statements from recent divisor-based treatments of the Erdős–Straus conjecture. It distinguishes proved certificate theorems from unresolved universal-coverage claims.

## 1. Kyle Bradford, *Elemental Patterns from the Erdős Straus Conjecture*

- Author: Kyle Bradford
- arXiv: `2403.16047`
- Initial version: 24 March 2024
- Source: https://arxiv.org/abs/2403.16047

### Type-II sufficient condition

For a prime `p`, suppose there is a positive integer `x` with

```text
ceil(p/4) ≤ x ≤ ceil(p/2),
```

and a positive divisor `q ∣ x²` such that

```text
q ≤ x,
q ≡ -x (mod 4x-p).
```

Then the paper defines

```text
y = p(x+q)/(4x-p),
z = p(x+x²/q)/(4x-p),
```

and proves that these are positive integers satisfying

```text
x ≤ y ≤ z,
p ∣ y,
4/p = 1/x + 1/y + 1/z.
```

The paper also derives the converse parametrization for Type-II solutions.

### What remains open

The universal assertion that every prime admits either the Type-I or Type-II divisor certificate is stated as **Conjecture 1**, not proved. Therefore the parametrization is an exact reduction/certificate theorem, not a proof of Erdős–Straus.

### Strict-order issue

Bradford's result gives weak order `x ≤ y ≤ z`. Our Formal Conjectures target requires

```text
1 ≤ x < y < z.
```

The formal bridge must either prove strictness from strengthened hypotheses or separately handle equality cases. The current factor-pair library obtains strictness from `a < b < p*s`.

## 2. M. Bello-Hernández, M. Benito, E. Fernández,
## *A Divisor Parametrization for the Erdős–Straus Conjecture*

- arXiv: `2606.10922`
- Version inspected: June 2026
- Source: https://arxiv.org/abs/2606.10922

### Proved contribution

The paper defines a divisor-based function `fab(n,a,b)` and proves that admissible parameters recover exactly decompositions of `1/n` whose three denominators are divisible by a prescribed integer; after scaling, the case `m=4` gives Erdős–Straus decompositions. It compares this framework with Type-I/II and continued-fraction-source constructions.

### Finite computation

The abstract reports that every tested prime

```text
p ≡ 1 (mod 4),
p < 10^14
```

was detected by `fab(p,a,b)` with

```text
1 ≤ a,b ≤ 11,
```

while warning that some composite values require larger parameters. This is large finite evidence, not universal coverage.

### Useful structural signal

The paper places multiple earlier constructions inside one divisor framework. This supports the project's decision to treat divisor structure as the primary language, but no bounded-parameter theorem for all primes is established.

## 3. Normalization target for Lean

To connect Bradford's Type-II certificate to the existing factor-pair library, rename Bradford's divisor to `q` and set the offset

```text
D = 4x-p.
```

Assume:

```text
0 < p,
0 < x,
0 < q,
q < x,               -- strengthened for strict order
q ∣ x²,
D ∣ q+x,
Nat.Coprime D x.
```

Let

```text
g = gcd(x,q),
a = q/g,
b = x/g.
```

The intended normalization proof is:

1. `g ∣ x` and `g ∣ q`, so write `x=g*b` and `q=g*a`.
2. `gcd(a,b)=1` after dividing by `g`.
3. From `q ∣ x²`, derive `a ∣ g*b²`.
4. Since `gcd(a,b²)=1`, cancel `b²` and obtain `a ∣ g`.
5. Write `g=a*c`; hence
   ```text
   q=a²c,
   x=abc.
   ```
6. The strict inequality `q<x` becomes `a<b` after cancelling the positive `g`.
7. From `D ∣ q+x`, obtain
   ```text
   D ∣ g(a+b).
   ```
8. Since `g ∣ x` and `gcd(D,x)=1`, also `gcd(D,g)=1`; cancel `g` to get
   ```text
   D ∣ a+b.
   ```
9. Therefore `(a,b)` witnesses `HasOppositeCoprimeDivisors x D`.
10. With `p+D=4x` and `D<p`, apply the existing strict Type-II theorem.

## 4. Universal obligation after formalization

Even after the normalization is kernel checked, the unresolved statement remains:

> For every residual prime `p ≡ 1 mod 24`, find an `x` and divisor `q ∣ x²` satisfying the required offset congruence and strictness hypotheses.

Neither paper discharges this universal quantifier. Any final proof must establish it, replace it with another universal coverage theorem, or prove a different route entirely.
