# Divisor-Certificate Literature Audit

## Scope

This note extracts reusable exact statements from recent divisor-based treatments of the Erdős–Straus conjecture. It distinguishes proved certificate theorems from heuristic, finite, or incomplete universal-coverage claims.

## 1. Kyle Bradford, *Elemental Patterns from the Erdős Straus Conjecture*

- Author: Kyle Bradford
- arXiv: `2403.16047`
- Initial version: 24 March 2024
- Source: `https://arxiv.org/abs/2403.16047`

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

The current factor-pair library obtains strictness from strengthened factor inequalities.

## 2. Andres Ventas, *A Ceiling Continued Fraction Approach to the Erdős–Straus Conjecture: Heuristic finiteness of counterexamples*

- arXiv: `2605.04551`
- Version inspected: v2, 25 May 2026
- Source: `https://arxiv.org/abs/2605.04551`

### External-source theorem

Ventas' Theorem 2.3 states a sufficient condition for a prime `p≡1 mod4`: if there exist positive integers `i,d` with

```text
d ∣ p+i,
d ≡ 3 mod4,
4i ∣ p+d,
```

then a three-term decomposition exists. Writing

```text
s=(p+i)/d,
c=(p+d)/(4i),
```

this is exactly the project's fixed-`a`, unit-`b` Type-I family with

```text
a=i,
p+a=d*s,
p+d=4*a*c.
```

The special case `i=1` is the unit gate from divisors of `p+1` congruent to `3 mod4`.

### What is proved and what is heuristic

The source theorem is an exact sufficient certificate. The paper does not prove that every residual prime has a successful source. Its global argument models shifted-divisor events as approximately independent and derives heuristic failure estimates. It reports large computational stress tests with early termination, but these are not a finite reduction or a universal proof.

### Project consequence

The fixed-`a` family must be credited as Ventas' external-source/FCT construction, not presented as a newly discovered parametrization. The project's distinct contributions are:

- exact strict-order hypotheses and polynomial certificates;
- Lean formalization of the general fixed-`a` theorem and its offset specialization;
- formally proved failure obstructions for `p+1` and `p+2`;
- exact profiling and falsification of candidate uniform bounds;
- integration with Type-II, complete factorization, and corrected divisor automata.

## 3. M. Bello-Hernández, M. Benito, E. Fernández,
## *A Divisor Parametrization for the Erdős–Straus Conjecture*

- arXiv: `2606.10922`
- Version inspected: v1, 9 June 2026
- Source: `https://arxiv.org/abs/2606.10922`

### Proved contribution

The paper defines a divisor-based function `fab(n,a,b)` and proves that admissible parameters recover exactly decompositions of `1/n` whose three denominators are divisible by a prescribed integer; after scaling, the case `m=4` gives Erdős–Straus decompositions. It compares this framework with Type-I/II and continued-fraction-source constructions.

### Relation to Ventas and the project

Proposition 17 identifies Ventas' condition

```text
d ∣ p+i,
d ≡ 3 mod4,
4i ∣ p+d
```

as exactly a sufficient certificate in the `b=1` layer of `fab(p,i,b)`. Its denominators after scaling are

```text
x=(p+d)/4,
y=(p+d)(p+i)/(4d),
z=p(p+d)(p+i)/(4id),
```

which agree with the project's fixed-`a` Type-I denominators.

The paper also notes that fixing finite sets of most Type-I/II parameters cannot by itself produce a congruence cover for every prime `p≡1 mod4`. This agrees with the project's modulo-9240 fixed-`a` affine audit: the dynamic divisor search is materially stronger than a finite list of fixed affine families.

### Finite computation

The paper reports that every tested prime

```text
p ≡ 1 mod4,
p < 10^14
```

was detected by `fab(p,a,b)` with

```text
1 ≤ a,b ≤ 11.
```

This is large finite evidence, not a bounded-parameter theorem. The paper explicitly warns that some composite values require larger parameters.

### Universal status

The paper proves completeness of its parametrization for the class of decompositions it encodes; it does not prove that an admissible parameter pair exists for every prime. The Erdős–Straus conjecture remains open within that framework.

## 4. Kyle Bradford, *A solution to the Straus–Erdős conjecture*

- arXiv: `2602.11774`
- Version inspected: v1, 12 February 2026
- Source: `https://arxiv.org/abs/2602.11774`

### Claimed scope

The abstract claims a solution for every prime, with weakly ordered denominators `x≤y≤z`.

### Decisive gap

The paper derives sufficient residue families and then states:

```text
The last thing that we must show is that this is a covering system.
```

It immediately follows that sentence with an observation about the first few primes congruent to `1 mod4`, and the paper then ends with the references. No theorem or proof establishes that the displayed residue families cover every prime `p≡1 mod4`.

Therefore this manuscript does not supply a complete universal proof. It also does not address the project's stricter requirement `1≤x<y<z` as a universal conclusion.

### Project decision

Do not treat arXiv `2602.11774` as resolving the conjecture. Its individual residue identities may be checked and reused as certificate families, but the missing covering-system theorem is exactly the universal obligation.

## 5. Normalization target for Lean

To connect Bradford's Type-II certificate to the existing factor-pair library, rename Bradford's divisor to `q` and set the offset

```text
D = 4x-p.
```

Assume:

```text
0 < p,
0 < x,
0 < q,
q < x,
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

The normalization proof is:

1. `g ∣ x` and `g ∣ q`, so write `x=g*b` and `q=g*a`.
2. `gcd(a,b)=1` after dividing by `g`.
3. From `q ∣ x²`, derive `a ∣ g*b²`.
4. Since `gcd(a,b²)=1`, cancel `b²` and obtain `a ∣ g`.
5. Write `g=a*c`; hence `q=a²c` and `x=abc`.
6. The strict inequality `q<x` becomes `a<b` after cancelling positive `g`.
7. From `D ∣ q+x`, obtain `D ∣ g(a+b)`.
8. Since `g ∣ x` and `gcd(D,x)=1`, cancel `g` to get `D ∣ a+b`.
9. Therefore `(a,b)` witnesses the opposite-coprime-divisor condition.
10. With `p+D=4x` and `D<p`, apply the strict Type-II theorem.

This normalization is already implemented in the current Lean stack.

## 6. Universal obligation after formalization

The literature now gives two broad exact certificate languages:

```text
Type-II / divisor-square:
  q ∣ x_k²,
  q ≡ -x_k mod d_k;

Ventas/FCT / fixed-a Type-I:
  d ∣ p+a,
  4a ∣ p+d.
```

The missing theorem is still universal coverage. A complete proof must show that every residual prime activates one of these exact mechanisms, prove that sufficiently many simultaneous failures are inconsistent, or derive a strict descent. Heuristic independence, density-one results, finite searches, and incomplete covering-system assertions do not discharge that obligation.
