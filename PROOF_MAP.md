# Proof Map

## Exact targets

The Formal Conjectures target is the stronger ordered statement for `n > 2`:

```text
∀ n ∈ ℕ, 2 < n → ∃ x y z ∈ ℕ,
  1 ≤ x ∧ x < y ∧ y < z ∧
  4 / n = 1 / x + 1 / y + 1 / z.
```

The ordinary Erdős–Straus conjecture is:

```text
∀ n ∈ ℕ, 2 ≤ n → ∃ x y z ∈ ℕ,
  0 < x ∧ 0 < y ∧ 0 < z ∧
  4 / n = 1 / x + 1 / y + 1 / z.
```

The endpoint `n=2` is handled by `(x,y,z)=(1,2,2)`. Strictly ordered denominators are impossible at `n=2`, so the strict target must not be stated with `2 ≤ n`.

## Established dependency chain

1. `HasDistinctDecomposition n`
   - polynomial integer identity;
   - strict denominator inequalities.
2. `HasDistinctDecomposition.toRational`
   - converts the polynomial identity to the exact rational statement.
3. Elementary residue families
   - remove all non-`1 mod 24` cases.
4. Scaling and prime reduction
   - any counterexample with `n > 2` implies a prime counterexample congruent to `1 mod 24`.
5. Type-II factor-pair and divisor-square normalizations
   - reusable sufficient criteria for strict decompositions.
6. Mordell reduction
   - a prime counterexample must lie in six classes modulo `840`.
7. Modulo-11 and corrected modulo-9240 reduction
   - a prime counterexample must lie in 34 classes modulo `9240`.
8. Final conditional bridge
   - `ResidualPrimeCoverage` implies the complete strict theorem for `n > 2`;
   - the strict theorem plus the explicit `n=2` identity implies the ordinary conjecture for every `n ≥ 2`.

## Exact remaining universal obligation

```lean
def ResidualPrimeCoverage : Prop :=
  ∀ p : ℕ, p.Prime → IsModNineTwoFourZeroResidue (p % 9240) →
    HasDistinctDecomposition p
```

This is not an accepted lemma. It is the explicit remaining theorem-strength gap.

## Acceptance rule for new lemmas

A lemma enters this map only after:

1. a precise statement with all arithmetic side conditions;
2. independent algebraic verification;
3. structured computational falsification attempts when applicable;
4. a clear deductive edge toward the exact target;
5. Lean compilation when formalized;
6. an axiom audit showing no `sorryAx` or introduced axioms.

Equivalent reformulations of `ResidualPrimeCoverage` are not progress unless accompanied by a genuinely new proof mechanism.
