# Failed and Blocked Approaches

A route is recorded here when it stalls at a theorem-strength missing lemma, is circular, is falsified, or cannot cover every integer.

## Status labels

- **FALSIFIED** — an explicit counterexample defeats the proposed lemma.
- **BLOCKED** — the route ends at an unproved statement essentially as strong as the conjecture.
- **PARTIAL** — correct but leaves infinitely many cases.
- **COMPUTATIONAL ONLY** — finite evidence with no theorem reducing the problem to a finite set.
- **DUPLICATE** — equivalent to an already registered mechanism without a new proof.

## Current registry

### Fixed finite offset bounds

**Status:** FALSIFIED as universal bounds; computationally useful only.

The exact searches refuted the empirical universal hypotheses `k ≤ 26` and `d ≤ 107`; the record at `p = 153633769` requires first witness `k = 31`, `d = 127`.

Do not revive a fixed-bound claim without a new theorem and adversarial testing beyond the known record.

### Mordell residue reduction

**Status:** PARTIAL.

The reduction to six classes modulo `840` is rigorous and valuable, but does not prove those classes. It is not a complete solution.

### Corrected modulo-9240 sieve

**Status:** PARTIAL.

The reduction to 34 classes modulo `9240` and the corrected `1201` and `6001` families are rigorous once CI passes. The remaining classes are infinite and cannot be discharged by finite computation alone.

### ResidualPrimeCoverage

**Status:** BLOCKED.

This statement is deliberately isolated as the exact final obligation. Merely renaming, reformulating, or assuming it is circular and does not count as progress.

### Finite verification through any numerical bound

**Status:** COMPUTATIONAL ONLY.

Such verification may falsify candidate lemmas and discover structure. It cannot prove the universal theorem unless accompanied by a proved finite-obstruction theorem.

### Density, heuristic, or probabilistic coverage

**Status:** BLOCKED for the exact target.

Showing density one, almost-all coverage, or high probability leaves possible exceptions and cannot establish the universal quantifier.

## Reopening rule

A blocked family may be reopened only when a researcher supplies a materially new construction, invariant, descent, local-global argument, finite-obstruction theorem, or contradiction mechanism—not merely a cleaner restatement of the same gap.
