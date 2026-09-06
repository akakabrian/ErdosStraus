/-
The unchanged conclusion requested by the review packet.
This file defines a target; it DOES NOT prove the abundance theorem.
The elementary restriction lemma at the end has an uncompiled proof body.
Target toolchain: Lean 4.27.0 / mathlib v4.27.0.
-/
import Mathlib

set_option autoImplicit false

namespace PrimeAbundance

structure StrictTriple (n : ℕ) where
  x : ℕ
  y : ℕ
  z : ℕ
  x_pos : 0 < x
  y_pos : 0 < y
  z_pos : 0 < z
  xy : x < y
  yz : y < z
  egypt : (4 : ℚ) / (n : ℚ) =
    1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)

def TypeII {n : ℕ} (t : StrictTriple n) : Prop :=
  n ∣ t.y ∧ n ∣ t.z ∧ Nat.gcd n t.x = 1

def HasAtLeastTypeIISolutions (n r : ℕ) : Prop :=
  ∃ f : Fin r → StrictTriple n, Function.Injective f ∧ ∀ i, TypeII (f i)

noncomputable def requestedMultiplicity (c : ℝ) (p : ℕ) : ℕ :=
  ⌊c * (Real.log (p : ℝ)) ^ 3 / Real.log (Real.log (p : ℝ))⌋₊

noncomputable def badPrimes (c : ℝ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 2 N).filter fun p =>
    Nat.Prime p ∧ ¬ HasAtLeastTypeIISolutions p (requestedMultiplicity c p)

def primesUpTo (N : ℕ) : Finset ℕ :=
  (Finset.Icc 2 N).filter Nat.Prime

/-- Original requested exceptional-count scale, not the stronger proposed one. -/
noncomputable def originalExceptionalScale (N : ℕ) : ℝ :=
  (N : ℝ) * (Real.log (Real.log (N : ℝ))) ^ 3 / (Real.log (N : ℝ)) ^ 3

/-- This is a proposition, not a theorem declaration. It has no mean/overlap premises.
The relative density assertion uses the actual prime count, not the integer count.
Small logarithms are harmless: the quantitative estimate is only eventual. -/
def PrimeAbundanceClaim : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ, 3 ≤ N₀ ∧
    (∀ N : ℕ, N₀ ≤ N →
      ((badPrimes c N).card : ℝ) ≤ C * originalExceptionalScale N) ∧
    Filter.Tendsto
      (fun N : ℕ => ((badPrimes c N).card : ℝ) / ((primesUpTo N).card : ℝ))
      Filter.atTop (nhds (0 : ℝ))

/-- Restrict an actual injection; no finiteness of the full solution type is assumed. -/
theorem hasAtLeast_mono (n r s : ℕ) (hrs : r ≤ s)
    (hs : HasAtLeastTypeIISolutions n s) : HasAtLeastTypeIISolutions n r := by
  rcases hs with ⟨f, hf, hII⟩
  let j : Fin r → Fin s := fun i => ⟨i.val, lt_of_lt_of_le i.isLt hrs⟩
  have hj : Function.Injective j := by
    intro i k h
    apply Fin.ext
    exact congrArg (fun x : Fin s => x.val) h
  exact ⟨f ∘ j, hf.comp hj, fun i => hII (j i)⟩

end PrimeAbundance
