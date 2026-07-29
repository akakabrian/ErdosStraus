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

### Distinct-prime-factor count forces the `d=11` gate

**Status:** FALSIFIED.

The proposed shortcut “five distinct prime factors of `x` force opposite coprime divisors modulo `11`” is false. Five distinct primes all congruent to `1 mod 11` leave every divisor congruent to `1 mod 11`, so no two coprime divisors can sum to `0 mod 11`.

The exact state variable is the closure of disjoint prime-power residue assignments, not the number of distinct prime factors. See `docs/fixed-gate-automaton.md` and `scripts/fixed_gate_automaton.py`.

### Entire prime-power components form an exact `d=11` automaton

**Status:** FALSIFIED.

The former specialized `d=11` model assigned only the entire component `q^e` to one side and required both divisor supports to be nonempty. Exact coprime divisors may instead use any exponent `q^j`, `1 ≤ j ≤ e`, on at most one side, and either divisor may equal `1`.

Two explicit counterexamples are:

```text
x=1849=43^2:       (a,b)=(1,43) works modulo 11;
p=4201, x_2=1053: (a,b)=(9,13) works modulo 11.
```

The second example survives the exact `d=3` and `d=7` gates and uses `3^2` from a `3^4` factor. Through `p≤10^7`, the legacy model missed 1,124 exact `d=11` successes after the first two gates failed. See `docs/D11_COMPONENT_AUTOMATON.md` and `data/d11-legacy-audit-10m.json`.

### Unit Type-I divisors of `p+1` prove universal coverage

**Status:** PARTIAL.

The gate is rigorous: an offset `d≡3 mod4` dividing `p+1` produces a strict Type-I decomposition. It does not cover primes for which every odd prime factor of `p+1` is `1 mod4`. Exact computation through `10^8` covered 398,283 of 719,781 residual primes and left 321,498 outside this family.

Do not reinterpret the finite 55.33% coverage rate as a universal theorem. The value of the gate is the new necessary splitting condition on a hypothetical counterexample and its unbounded-offset character.

### The unit gate plus a short bounded offset block is universal

**Status:** FALSIFIED for the tested bounds.

The claim with offsets `k≤10` is defeated by

```text
p=496609,
p+1=2*5*53*937,
first complete consecutive-offset witness k=12.
```

The claim with offsets `k≤25` is defeated by

```text
p=8803369,
p+1=2*5*880337,
first complete consecutive-offset witness k=26.
```

The absence of an unresolved case through `10^8` at `k≤26` is computational only and is not promoted to a universal bound.

### Type-I adds no witness before Type-II

**Status:** FALSIFIED.

For

```text
p=386401,
```

the first complete witness occurs at `k=2` in the Type-I branch, while the first Type-II witness occurs at `k=13`. Through `10^8`, 1,590 residual primes acquired an earlier first witness after the complete `p`-adic factor split was searched.

### A fixed finite bound on the fixed-`a` parameter

**Status:** COMPUTATIONAL ONLY.

Every tested residual prime through `10^8` had a fixed-`a` Type-I certificate with first `a≤890`; every tested Mordell-residual prime from `10^8` through `10^9` had first `a≤146`. No theorem bounds `a`, and the isolated `a=890` record gives no monotone law from which a finite reduction follows.

Do not state `a≤890`, `a≤1000`, or any other tested ceiling as a lemma without a proof that reduces all larger targets to the finite computation.

### Fixed-`a` affine families close the modulo-9240 residual set

**Status:** PARTIAL with no gain on the existing hard classes.

Restricting to fixed pairs `(a,d)` with `4a|9240` and `d|9240` covers 190 of the 240 unit residues congruent to `1 mod24`, leaving 50. Every one of the existing 34 Type-II residual classes survives this fixed-`a` affine sieve.

Thus the strong dynamic fixed-`a` coverage is not explained by another finite affine residue cover at modulus `9240`; it depends on the actual divisor structure of `p+a`.

## Reopening rule

A blocked family may be reopened only when a researcher supplies a materially new construction, invariant, descent, local-global argument, finite-obstruction theorem, or contradiction mechanism—not merely a cleaner restatement of the same gap.
