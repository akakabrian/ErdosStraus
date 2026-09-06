# Proof-source map and exact mathematical obligations

The entries below describe the source dependency chain verified on 6 September
2026. The guarded fresh-source run compiled all 24 local files and accepted the
required axiom reports. The earlier source reviews found and repaired a missing
determinant helper, wrong API namespaces, and other proof-body defects; see
`REVIEW_FINDINGS.md` for that historical pre-verification record.

## 1. Final target and witness arithmetic

`Target.lean` preserves the earlier claim exactly. `Arithmetic.lean` and `Packets.lean` define genuine restricted packets, prove source-level parameter recovery, and retain the actual roughness cutoff and unordered distinct-row overlap.

For `Q=12abu-1`, `Q'=12cev-1`, and `D=ae-cb`, the algebraic identities are

```
4be(s-s') = aeQ - cbQ' + D
(4be)(36acuv) - 1 = QQ' + Q + Q'.
```

The second identity gives an inverse of `4be` modulo every common divisor of `Q,Q'`. Thus compatibility is equivalent to `d | D` at the **full modulus d**, with no squarefree reduction. Distinct reduced rays have nonzero determinant, of absolute value below `B²`. The previously missing `Late.determinant_ne_zero` is now explicitly proved in `Arithmetic.lean` from `reduced_ray_unique`.

## 2. Finite analytic foundations

| Modules | Main implemented results |
|---|---|
| `Sums.lean` | Harmonic sums, positive covers and weighted injections, cubic AM-GM, reciprocal-square tails, dyadic decomposition. |
| `ReciprocalBlocks.lean`, `Residues.lean` | Literal `abs(count-H/q) ≤ 1`, upper and lower counts, products of excluded primes, distinct-subset product injection. |
| `Bonferroni.lean`, `TensorSums.lean` | Finite inclusion-exclusion signs, geometric remainder, finite coordinate moments and Markov splitting. |
| `Sieve.lean` | Coefficient-uniform finite linear sieve, retaining errors for intersections whose moduli exceed the interval length. |
| `PrimeProduct.lean` | A weak Mertens lower bound from finite exponent tuples and mathlib's proved Chebyshev upper bound. |
| `RayMass.lean` | Harmonic mass retained after discarding the small primitive rays. |

For `w ≥ 2`, write

```
k = 8*(Nat.log 2 w + 1)
D(w) = 4*w^(k+2)
V_c(w) = product_{p≤w, p prime, p∤c} (1-1/p).
```

The implemented absolute sieve estimate is

```
|S(c;U,H;w)-H*V_c(w)| ≤ w^(k+1) + H*w²/2^(k+1).
```

The endpoint count uses an injection of prime subsets into their distinct products, not a false assertion that all their moduli are small. Since `4w³ ≤ 2^(k+1)`, length `H ≥ D(w)` yields

```
H*V_c(w)/2 ≤ S(c;U,H;w) ≤ 3H*V_c(w)/2.
```

The prime-product module implements

```
V(w) ≥ 1 / (mertensConstant * log w)
mertensConstant = 4*(1/log 2 + 16) > 0.
```

It uses a finite exponent range `0,...,w` at each prime. No limit of an infinite Euler product is assumed.

## 3. Mean lower bound for the actual selected packets

`ScaleSums.lean` reindexes the actual packet sum using the injective parameterization. It proves a lower bound by `2n` disjoint dyadic scale blocks and harmonic ray mass. Both the cutoff and the finite packet family are the concrete definitions, not constrained abstract functions.

For `B=2^n`, the source derives

```
w_n ≥ (4n)^100
w_n ≤ (8n)^100
log w_n ≤ 400 log(n+1)
rayCutoff(2^n) ≤ n²+2
D(w_n) ≤ B^4                                     eventually
rayMass(n²+2, 2^n) ≥ n²/32                        eventually.
```

Hence, with `A=307200*mertensConstant`,

```
mean(2^n) ≥ n³/(A log(n+1))                       eventually.
```

The denominator is eventually positive; the mean is positive and the integer thresholds are not restricted to zero. The growth step uses proved log-versus-power little-o lemmas from mathlib, not an assumption about the selected mean.

## 4. Overlap: enough for the unchanged original theorem

`DivisorMoments.lean` distinguishes pointwise cubes from Dirichlet convolution and implements

```
tau(n)^3 ≤ d_8(n)
sum_{m≤X} tau(m)^3 ≤ X*(1+log X)^7.
```

`DeterminantMoment.lean` implements the finite harmonic energy bound

```
E(X) = sum_{1≤x,y≤X, x≠y} tau(x)tau(y)tau(|x-y|)/(xy)
E(2^(2n)) ≤ 4096*(n+1)^9.
```

It uses dyadic rectangles and the cubic AM-GM inequality. A positive difference has at most `2 min(U,V)` representations in a rectangle. The zero difference is excluded before the divisor function is used.

For different rays, every contributing full divisor satisfies `w<d<B²`. All scale values exceed `B⁴`. `ScaleSums.lean` gives the reciprocal progression bound, and `Overlap.lean` performs a positive full-divisor cover followed by the energy estimate.

For the same ray, `DivisorKernel.lean` proves a delayed weighted gcd kernel. When `2c ≤ B⁴`, its source bound is

```
G(c; B⁴+1, B⁶) ≤ 384*(n+1)^3/c².
```

No roughness is needed for that upper bound. Summation over rays converges by reciprocal squares. The source deliberately does not implement the stronger `O(1/log B)` overlap claim from the previous paper draft; it does not need that claim.

The actual restricted overlap is bounded in `Overlap.lean` by

```
overlap(2^n) ≤ 1536*(n+1)^3 + 131072*(n+1)^11/w_n.
```

`AnalyticBounds.lean` then derives `overlap(2^n) ≤ 2^34*n³` for `n≥3`.

Public combined output:

```
PrimeAbundance.Analytic.analytic_bounds
```

This theorem has no lower-mean, upper-overlap, or sieve premises.

## 5. Decoder and finite second moment

`Decoder.lean` implements integrality, `s | M*x`, strict order, Type-II divisibility, coprimality at primes, and recovery of the packet from a solution. This is the actual injection into the locked solution type.

`FiniteTransfer.lean` proves the finite implication for the **selected** family rather than substituting quantities into a theorem about the full family. Pair upper counts use full lcm divisibility; a CRT-existence theorem is not needed for an upper bound. It retains

```
variance ≤ mean + 2*overlap
bad offsets ≤ 4*[H*(mean+2*overlap)/mean² + (1+12B⁸)²].
```

The diagonal appears once. The overlap is unordered and receives its required factor two. The factor four multiplies the endpoint too. Positivity of the mean is explicit. The finite theorem admits the empty interval.

## 6. Quantitative conclusion and relative prime density

`GlobalAbundance.lean` takes

```
n = (Nat.log 2 N)/24
B = 2^n
A_start = 12B⁸+1
H = N.
```

Primes up to `A_start` are counted trivially. The later bad primes up to `N` inject into offsets of this single interval, avoiding a separate unproved global dyadic-union claim.

Explicit constants are

```
meanConstant        = 307200*mertensConstant
overlapConstant     = 2^34
varianceConstant    = meanConstant + 2*overlapConstant*meanConstant²
abundanceCoefficient= 1/(221184*meanConstant)
intervalPrefactor   = 4*varianceConstant+1000
abundanceBoundConstant = 110592*intervalPrefactor.
```

The implemented bounds give a count at most a constant times

```
N * log(n+1)² / n³,
```

which is bounded by the original, slightly weaker requested rate

```
N * (log(log N))³ / (log N)³.
```

The integer threshold uses natural floors on both sides of a proved real comparison. It is not an informal real-valued count.

`PrimeCount.lean` implements the explicit elementary inequality

```
N/(6 log N) ≤ #primesUpTo(N),                    N≥16,
```

using proved finite binomial-factorization lemmas. This is a lower bound, not a PNT premise. Dividing the bad count by this denominator and applying the log-power limit yields the actual relative-density conclusion.

Final implemented chain:

```
analytic_bounds
  -> global_count_at_index
  -> quantitative_abundance
  -> relative_density
  -> prime_abundance : PrimeAbundanceClaim.
```

All arrows here describe source dependencies. Acceptance of the Lean proofs awaits actual elaboration and the final axiom/type audit.
