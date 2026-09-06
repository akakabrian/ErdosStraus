# Second-pass review and repairs

## Verdict and scope

This second pass found concrete source and verification-harness defects. They have been repaired in this candidate. **No Lean parser, elaborator, compiler, or kernel was run.** The revised source is not a verified proof, and the repairs themselves still require elaboration.

The original target file and the exact final type/axiom check file are byte-for-byte unchanged. No desired analytic estimate was converted into a hypothesis, no numerical theorem bound was weakened, and no admission or new axiom was added. The final source declaration remains:

```lean
PrimeAbundance.prime_abundance : PrimeAbundance.PrimeAbundanceClaim
```

The review covered the supplied 24-file source chain, the proof map, the restricted-family argument, and the build/axiom harness. External checking was limited to relevant official mathlib API declarations, especially the pinned v4.27.0 asymptotics namespace. This is a self-review, not an independent referee report.

I found no mathematical counterexample to the abundance conclusion or the restricted-family route on this pass. That statement is a review judgment, not a proof certificate. The original full-family overlap estimate and ESC remain outside the result claimed by this candidate.

## 1. Definite source defects repaired

### Missing determinant lemma

`Overlap.lean` called `Late.determinant_ne_zero`, but the original archive contained no such declaration. An import-closure check cannot detect a missing declaration inside an existing imported module. This was a genuine missing piece of the delivered source.

The revised `Arithmetic.lean` now proves it from the already present `reduced_ray_unique`: if `ae-cb=0`, the positive coprime pairs `(a,b)` and `(c,e)` represent the same reduced fraction, hence are equal. The different-ray assumption contradicts that equality. The caller now passes precisely the positivity, coprimality, and distinct-ray hypotheses required by the new lemma.

This matters mathematically: the nonzero determinant is needed before applying the divisor-count bound to its absolute value. A zero determinant belongs to the separate same-ray case.

### Wrong namespace on two asymptotic calls

`AnalyticBounds.lean` and `GlobalAbundance.lean` used:

```lean
Real.isLittleO_log_rpow_rpow_atTop
```

In the pinned mathlib v4.27.0 source, that declaration is at the root, not inside `Real`. Both calls now use:

```lean
_root_.isLittleO_log_rpow_rpow_atTop
```

Reference checked: `Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean` at tag `v4.27.0`, the declaration beginning `theorem isLittleO_log_rpow_rpow_atTop` following the close of `namespace Asymptotics`. This is an API/source inspection, not an execution result.

### Mismatched summand in the totient split

The old `Overlap.gcd_le_twice_nontrivial_totient` attempted to rewrite an erased sum of `totient d` using an erased-sum formula instantiated with an `if`-valued summand. That formula did not match the sum being rewritten.

The revised proof splits the original summand pointwise for every positive divisor:

```text
phi(d) = (if d=1 then 1 else 0) + (if 1<d then phi(d) else 0).
```

Summation and `Nat.sum_totient` then give exactly

```text
sum_{d|g, d>1} phi(d) = g-1.
```

Every positive divisor is retained; this does not replace a full divisor sum by a squarefree sum. The subsequent bound `g <= 2*(g-1)` for `g>1` is unchanged.

## 2. Additional proof-body repairs and strengthening

These are explicit source repairs, not claims that their previous or replacement tactic scripts were compiler-tested.

| Module | Repair |
|---|---|
| `RayMass.lean` | Expand the square in the product-of-harmonic-sums identity explicitly. Prove injectivity by rewriting equal gcds and quotients before applying exact reconstruction equalities. |
| `FiniteTransfer.lean` | Expand `mean^2` explicitly rather than ending the product-of-sums identity with `rfl`. |
| `ScaleSums.lean` | Normalize the sum of `2n` block contributions explicitly, proving `2n*V/(48ab)=n*V/(24ab)`. Supply coefficient lower bounds and handle natural subtraction via an explicit product lower bound. |
| `Overlap.lean` | Explicitly normalize the outer factor two and inner factor sixteen in the divisor cover. Expand the reciprocal-square product identity and supply the coefficient bound for the gcd kernel. |
| `DivisorMoments.lean` | Propagate equality of quotients into exact division identities before proving injectivity. Normalize addition in the hockey-stick/Pascal identity instead of asking congruence to commute summands. |
| `DivisorKernel.lean` | Propagate the index equality before `omega`, make the natural-subtraction positivity argument explicit, and prove the ordered reciprocal denominator comparison using nonnegativity of the added term. |
| `GlobalAbundance.lean` | Replace a bare positivity call on `1 <= 1 + ...` with an explicit addition-order lemma. |

There are 21 recorded edit groups across nine Lean source files, including the new determinant lemma and the two namespace repairs. `logs/review-source-edits.json` records the edits; `CHANGES.patch` is the authoritative textual comparison with the earlier delivered archive.

## 3. Verifier defects reproduced and repaired

### Exact theorem names

The old axiom-report parser could accept a line for either of these names in place of the required final theorem:

```text
Unrelated.PrimeAbundance.prime_abundance
NotPrimeAbundance.prime_abundance
```

Its regular expression matched a suffix rather than a complete declaration name. The revised parser anchors the whole report line and requires the exact name. It still rejects missing and duplicate reports, `sorryAx`, and any axiom outside `propext`, `Classical.choice`, and `Quot.sound`.

### Exact Lean release

The old substring test accepted version strings `4.27.0-rc1` and `4.27.01`. The revised guard parses a single version banner and requires the exact token `4.27.0`.

These false accepts were reproduced with synthetic inputs and are recorded in `logs/review-old-guard-reproductions.json`. No real Lean verification report existed or was forged; these are defects in the acceptance harness, not evidence of a previously accepted false proof.

### Fresh, attributable local compilation

The revised wrapper stages only audited `.lean` files in a temporary source tree, compiles into a separate new object directory, and requires a fresh nonempty `.olean` for every expected local module. Source-adjacent cached objects are not copied.

Lake search paths may be relative to the matching workspace. The runner now resolves them against that workspace before changing directories to the staged sources, and prepends the fresh local object directory. This avoids accidentally resolving upstream paths against the staging directory.

The wrapper records and compares hashes for source and execution-support files, locks `GoalCheck.lean` as well as `Target.lean`, and uses unique run directories. It writes a success report only after all compilation, type, and axiom checks succeed. None of that execution path has run here. Cached upstream mathlib is still allowed; this is not a complete source rebuild of mathlib or a security proof of the entire software toolchain.

### Stronger static checks, with explicit limits

The source audit now checks 151 explicitly qualified local references of the forms `Late.foo` and `Analytic.foo`, including their transitive import availability. This would detect the missing-determinant-helper class of error. It also rejects unsupported import forms instead of silently skipping them, output-producing commands outside locked `GoalCheck.lean`, and the kernel-check bypass option.

It remains a limited lexical check. It does not resolve every unqualified name, validate external APIs generally, parse Lean completely, or verify tactics. Passing it is not theorem acceptance.

## 4. An exact regression that detects the factor-of-two and prime-power mistakes

Take authentic original packets `(M,s)=(333,1)` and `(696,1)` with auxiliary cutoff zero. Then

```text
Q  = 1331 = 11^3
Q' = 2783 = 11^2 * 23
gcd(Q,Q') = 121
lcm(Q,Q') = 30613.
```

Their mean, unordered overlap, and period variance are

```text
mu    = 34/30613
Delta = 1/30613
v     = 1100912/937155769.
```

Exact arithmetic gives

```text
v > mu + Delta
v <= mu + 2*Delta.
```

Thus this test actually fails when the unordered-overlap multiplier two is lost; it does not merely check a case where either convention would pass. The joint firing probability is `121/(1331*2783)`, so replacing the full gcd by its radical `11` undercounts by a factor of eleven.

Additional interval tests check the lower first-moment error, upper second-moment error, the normalized-square endpoint `2m/mu + m^2/mu^2`, and the outer lower-tail multiplier four, including `H=0`. Same-row tests retain multiple strict labels and check their incompatibility.

These are finite tests with auxiliary cutoffs, not samples of the enormous eventual actual-cutoff regime, and not proofs of the asymptotic theorem.

## 5. Preparation checks actually run

All of the following passed after the repairs:

- The original 20,107 grouped exact-arithmetic regression cases.
- Eighteen review test methods for source/harness controls; these include sixteen synthetic axiom-parser cases.
- 7,181 additional finite arithmetic cases: 4,095 full-divisor splits, 2,193 hockey-stick identities, 832 block-coefficient identities, 60 interval-moment cases, and one full-prime-power intersection example.
- Updated lexical/source audit: 24 Lean files, 5,406 source lines, 279 theorem/lemma bodies, and 151 qualified local references checked.
- Python syntax compilation of helper scripts and Bash syntax checking of `verify.sh`.

The counts describe test coverage, not degrees of confidence or proof completeness. Some checks share underlying examples. Logs are included. Older first-delivery metadata and logs are preserved as historical records; use `review-*` reports and the current `STATUS.json` for this pass.

## 6. Correct interpretation and next acceptance gate

The earlier audit was too shallow to support any suggestion that presence of all proof bodies meant a runnable formalization. The missing helper and wrong namespace make that particularly clear. The right description is **an end-to-end uncompiled implementation attempt, now repaired and more carefully reviewed**.

The exact target is preserved:

```text
SHA-256(Target.lean):
ebf6aa06a5b76c59b1079f357e8bcf596b52a345146bbd2fd213a5c2e79187da
```

The strict Type-II injection, actual packet cutoff, full prime powers, unordered distinct-row convention, diagonal once, overlap factor two, and literal endpoint `4*(1+12*B^8)^2` are unchanged. The selected-family proof still does not supply the original full-family overlap bound.

Run the revised package in a clean directory with the pinned workspace:

```bash
bash verify.sh /absolute/path/to/the/matching/lake-workspace
```

Require the final locked type, the entire fresh local import chain, and actual transitive axiom reports to pass. Additional syntax, API, tactic, or substantive proof repairs may still be needed. This review does not justify promising otherwise.
