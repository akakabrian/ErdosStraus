# Additional review of the repaired analytic Lean candidate

## Result and verification boundary

This review found further source-level defects in the previously repaired archive, and rewrote the affected proof bodies. The replacement source has **not** been parsed, elaborated, compiled, or checked by Lean. These are corrections justified by source inspection and elementary identities, not a record of successful Lean repairs. Other API, type, tactic, or mathematical errors may remain.

The input is `prime-abundance-analytic-reviewed.zip`, SHA-256:

```
d685a613dafdf8593c9963ee1da27c1f989eb9646ddf4358ea30a7b4a13fea0e
```

The output is `prime-abundance-analytic-reviewed-v2.zip`. It supersedes the input archive. This is another self-review, not an independent referee report.

Five Lean modules were changed: `Sums`, `TensorSums`, `PrimeProduct`, `Overlap`, and `FiniteTransfer`. Seven existing lemma bodies were edited and one finite-sum permutation helper was added. All **279 existing theorem/lemma signatures** match the input after comment/whitespace normalization. `Target.lean`, `Packets.lean`, `Main.lean`, and `GoalCheck.lean` are byte-for-byte unchanged. No desired analytic estimate was changed into a hypothesis, and no proof admission or new axiom was introduced.

The final source still targets:

```lean
PrimeAbundance.prime_abundance : PrimeAbundance.PrimeAbundanceClaim
```

No counterexample to the restricted-family mathematical route was established in this review. That is a limited review finding, **not** a certificate of the route. The original full-family overlap estimate and ESC remain outside the claim of this candidate.

## 1. Product-moment distribution: an already-consumed rewrite

In `TensorSums.product_weight_moment`, the old sequence was:

```lean
simp_rw [mul_sum]
rw [sum_comm, mul_sum]
```

The first line distributes multiplication over sums throughout the target, including its right side. After the sum permutation, trying to apply `mul_sum` again does not supply the intended additional transformation: it has already been performed. The revised source removes that second distribution and then applies the coordinate-moment identity.

This is a source-level mismatch, not a counterexample to the true finite product-moment inequality. The new exact tests include empty index sets, an empty coordinate domain, zero coordinate masses, and signed coordinate heights; the lemma only requires the weights to be nonnegative, not the heights.

## 2. Geometric induction: specify the summand and the endpoint

The weighted geometric identity formerly used two unrestricted `sum_range_succ` rewrites. After expanding the new weighted sum, the second rewrite can expand the shorter weighted sum on the left again instead of the unweighted sum on the right. That removes the expression the induction hypothesis is intended to handle.

The revised proof specializes the two rewrites to their distinct summands and to the new endpoint:

```lean
rw [sum_range_succ (fun j : ℕ => (j:ℝ)*r^j) (J+1),
    sum_range_succ (fun j : ℕ => r^j) (J+1), mul_add, ih]
rw [pow_succ r (J+1)]
```

The unweighted geometric identity also now explicitly expands the exponent `J+2`, rather than using an unrestricted power-successor rewrite that can select a lower power first. This latter change is a precision improvement as well as protection against rewrite-order fragility.

The mathematical identities remain exactly:

```
(1-r) * sum_{j=0}^J r^j = 1-r^(J+1)
(1-r) * sum_{j=0}^J j*r^j = r*sum_{j=0}^J r^j -(J+1)*r^(J+1).
```

## 3. Prime tuples: reindex the intended prime sum/product

`primeTuple_log_moment` used an unrestricted reverse `sum_coe_sort` after expanding the tuple weights. At that point the target has several finite sums; the first is the outer exponent-tuple sum, not the intended prime sum on the right. The analogous unrestricted reverse `prod_coe_sort` in `primeTupleMass_times_V` can act on the earlier product of geometric coordinate masses rather than `V(w)`.

The revised source proves typed equalities `hprimeSum`, `hV`, and `hresult`, explicitly converting exactly the prime-indexed expressions. All products can then be merged over the same subtype of primes.

The one-coordinate moment inequality also now explicitly factors out the nonnegative coefficient `log p`, multiplies the finite geometric-moment bound by it, and uses the exact identity

```
(1/p)/(1-1/p) = 1/(p-1).
```

The nonzero denominators are named. This is a proof-body strengthening, not a change to the weak Mertens constant or an invocation of an unproved Mertens input.

## 4. Different-ray overlap: the divisor sum was not outermost

This is the most consequential reindexing defect found. After removing the outer factor two, the old source had a triple sum in the order

```
sum_u sum_v sum_d F(u,v,d).
```

One `sum_comm` exchanges only `u` and `v`. The old proof then applied `sum_congr rfl` and introduced an index named `d` as though the divisor sum were already outermost. In general, the scale range and divisor set are different, so that step cannot identify the intended outer indexing sets.

The added helper explicitly proves the permutation

```
sum_u sum_v sum_d F(u,v,d) = sum_d sum_u sum_v F(u,v,d),
```

for **three potentially different index types**. It performs an inner interchange followed by the outer interchange. `diffCover_scale_sum` uses that equality before introducing `d`.

The separable scale weights are then factored using an explicit product-of-sums identity, with the `u` weight and `v` weight defined separately. This avoids the old ambiguous distribution order as well.

A small arithmetic diagnostic makes the index distinction visible. With scale indices in `{1,2}`, divisor indices in `{1,2,3}`, and `F(u,v,d)=u+10v+100d`, the correct fiber at `d=1` has sum **466**, while the mistakenly identified fiber at `v=1` has sum **1269**. This is **not** a counterexample to interchanging finite sums (their total sums do agree); it demonstrates that the outer fiber was being identified with the wrong index.

All full divisors, including prime powers, remain in the cover. No factor of two is removed or added to the overlap definition.

## 5. Second-moment aggregation: display the four sums before collecting them

`FiniteTransfer.second_moment_upper` attempted to normalize the summed pair budget with

```lean
simp_rw [sum_add_distrib, ←mul_sum]
rw [hbase,hdiag,hforward,hbackward]
```

That is not a reliable way to expose precisely the four named double sums. Pulling a multiplier outside can expose a previously unexpanded sum of addends; if applied more broadly, reverse distribution can instead consume a base sum before `hbase` is used. The revised source gives an explicit intermediate equality with the base, diagonal, forward-overlap, and reverse-overlap sums all displayed, and normalizes the two sides by **forward** distribution.

It then applies the four named identities. The budget remains

```
H*(mean^2 + mean + 2*overlap) + packet_count^2.
```

The diagonal is counted once. The unordered overlap appears twice because both orientations are summed. The residue-count endpoint allowance remains one for each ordered pair, giving `packet_count^2`. No finite bound, positive-mean hypothesis, or subsequent factor-four endpoint term is weakened.

## 6. Source locations

Line numbers are declaration-start locations in the input and output archives.

| File | Declaration | Input line | Revised line |
|---|---|---:|---:|
| `TensorSums.lean` | `product_weight_moment` | 55 | 55 |
| `TensorSums.lean` | `finite_geometric_identity` | 72 | 73 |
| `TensorSums.lean` | `finite_geometric_moment_identity` | 80 | 83 |
| `PrimeProduct.lean` | `primeTuple_log_moment` | 162 | 162 |
| `PrimeProduct.lean` | `primeTupleMass_times_V` | 190 | 203 |
| `Sums.lean` | `sum_rotate_three` | New | 19 |
| `Overlap.lean` | `diffCover_scale_sum` | 249 | 249 |
| `FiniteTransfer.lean` | `second_moment_upper` | 256 | 256 |

## 7. Checks actually executed

The original exact-arithmetic suite passed **20,107 grouped cases**. The prior review suite again passed **18 test methods** and **7,181 additional arithmetic cases**; its axiom-parser tests are synthetic, not actual Lean axiom reports.

The new `review2_tests.py` passed **9 known-pattern/target-lock test methods** and **1,043 exact finite arithmetic cases**:

| Group | Cases |
|---|---:|
| Geometric identities, weighted moments, and endpoint recurrences | 168 |
| Tensor moments, including empty and zero-mass cases | 100 |
| Prime-tuple product and coordinate-moment identities | 42 |
| Triple-sum rotations with distinct index types and unequal sizes | 125 |
| Full-divisor separable overlap identities with unequal scale ranges | 480 |
| Second-moment budget, diagonal, orientations, and endpoint term | 128 |

All arithmetic in those new tests is rational/integer exact. The prime-tuple moment tests use nonnegative integer coordinate coefficients to test the algebraic multiplication step, not numerical approximations to logarithms. The overlap identity tests permit auxiliary finite ranges; they do not purport to sample the enormous eventual actual-cutoff regime.

The static source hygiene audit, Python syntax checks, and Bash syntax check pass. **No Lean command was run.** The lexical signature comparison is not a type-checker, and the new known-pattern tests do not certify arbitrary rewrite sequences.

Relevant logs are under `logs/review2/`. Previous logs are retained as historical preparation records, not relabeled as results of this review.

## 8. Reproducibility and later acceptance

`REVIEW2_CHANGES.patch` is the patch from the input reviewed package to this revision, excluding package manifests, log snapshots, and the patch itself. A patch-application check reconstructs all included changed files from the input. The refreshed `PACKAGE_MANIFEST.json` records the output files except itself.

The same actual acceptance command applies in a fresh directory:

```bash
bash verify.sh /absolute/path/to/the/matching/lake-workspace
```

It must elaborate the complete local source chain and accept the unchanged final goal and real transitive axiom reports. A passing Python suite, a clean source scan, or this review is not a substitute. In particular, **I cannot conclude that no further fixes are needed** from this non-executing review.

## API references checked

The relevant finite distribution and successor identities were checked against the official mathlib **v4.27.0** source, not a claim based on a newer library version:

- `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`: `prod_range_succ` and its generated additive version `sum_range_succ`.
- `Mathlib/Algebra/BigOperators/Ring/Finset.lean`: `sum_mul`, `mul_sum`, and `sum_mul_sum`.

The subtype reindexing changes constrain the intended expression explicitly. This review does not claim that every external API reference in the 24-file development was independently revalidated.
