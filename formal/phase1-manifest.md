# Phase 1 Formalization Manifest

## Integration source

Repository: `akakabrian/formal-conjectures`

Branch: `erdos-242-phase1`

Current audited head: `e63496b0bd64b9383df186e09a9999940d623f66`

Draft PR: https://github.com/akakabrian/formal-conjectures/pull/2

## Files

```text
FormalConjecturesForMathlib/NumberTheory/ErdosStraus/Basic.lean
FormalConjecturesForMathlib/NumberTheory/ErdosStraus/ElementaryFamilies.lean
FormalConjecturesForMathlib/NumberTheory/ErdosStraus/Scaling.lean
FormalConjecturesForMathlib/NumberTheory/ErdosStraus/Reduction.lean
FormalConjecturesForMathlib/NumberTheory/ErdosStraus/MinimalCounterexample.lean
FormalConjecturesForMathlib/NumberTheory/ErdosStraus/TypeIIFactorPair.lean
FormalConjecturesForMathlib/NumberTheory/ErdosStraus/DivisorResidues.lean
FormalConjecturesForMathlib/NumberTheory/ErdosStraus/SmallGates.lean
```

Workflow:

```text
.github/workflows/erdos-242-fast.yml
```

## Exact target

The main target is unchanged and remains open in:

```text
FormalConjectures/ErdosProblems/242.lean
```

```lean
theorem erdos_242 (n : ℕ) (hn : 2 < n) :
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
      (4 / n : ℚ) = 1 / x + 1 / y + 1 / z := by
  sorry
```

The Phase 1 files are helper libraries. They do not replace this `sorry` and do not claim the universal theorem.

## Theorem inventory

### `Basic.lean`

- `HasDistinctDecomposition.hasDecomposition`
- `HasDistinctDecomposition.toRational`

### `ElementaryFamilies.lean`

- `even_family`
- `mod_three_two_family`
- `mod_four_three_family`
- `mod_eight_five_family`

### `Scaling.lean`

- `HasDecomposition.scale`
- `HasDistinctDecomposition.scale`

### `Reduction.lean`

- `hasDistinctDecomposition_of_mod_twenty_four_ne_one`
- `counterexample_mod_twenty_four_eq_one`

### `MinimalCounterexample.lean`

- `exists_prime_counterexample_one_mod_twenty_four`

### `TypeIIFactorPair.lean`

- `typeII_factor_pair_identity`
- `typeII_factor_pair_hasDecomposition`
- `typeII_factor_pair_hasDistinctDecomposition`

### `DivisorResidues.lean`

- `oppositeCoprimeDivisors_hasDistinctDecomposition`

### `SmallGates.lean`

- `oppositeCoprimeDivisors_three_of_divisor_mod_three_two`
- `dThree_gate_hasDistinctDecomposition`

## Required verification record

Before marking Phase 1 complete, record:

- targeted build command and run ID;
- full build command/workflow and run ID;
- warnings-as-errors result;
- `#print axioms` output for important theorems;
- search result for `sorry`, `admit`, `axiom`, `native_decide`, and unsafe declarations in the helper directory;
- immutable commit hash.
