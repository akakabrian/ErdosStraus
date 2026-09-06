/-
Uncompiled proof-source candidate: a concrete finite progression bound.
The first hit is included. The useful hypothesis q <= U is the delayed-scale
condition, not an assumed distribution estimate. This is not a sieve theorem.
-/
import Mathlib

set_option autoImplicit false
open scoped BigOperators

namespace PrimeAbundance
namespace Late

abbrev ResidueHits (q A H : ℕ) (r : ZMod q) :=
  {k : Fin H // ((A + k.val : ℕ) : ZMod q) = r}

/-- At most one hit in each q-sized OFFSET block. -/
theorem residueHits_card_le (q A H : ℕ) (hq : 0 < q) (r : ZMod q) :
    Nat.card (ResidueHits q A H r) ≤ H / q + 1 := by
  classical
  letI : NeZero q := ⟨hq.ne'⟩
  let f : ResidueHits q A H r → Fin (H / q + 1) := fun k =>
    ⟨k.val.val / q, Nat.lt_succ_of_le (Nat.div_le_div_right k.val.isLt.le)⟩
  have hf : Function.Injective f := by
    intro k l h
    have hd : k.val.val / q = l.val.val / q := congrArg Fin.val h
    have hr : ((A + k.val.val : ℕ) : ZMod q) =
        ((A + l.val.val : ℕ) : ZMod q) := k.property.trans l.property.symm
    have hc : (k.val.val : ZMod q) = (l.val.val : ZMod q) := by
      apply add_left_cancel (a := (A : ZMod q))
      simpa only [Nat.cast_add] using hr
    have hm : k.val.val % q = l.val.val % q := by
      have hv := congrArg (ZMod.val : ZMod q → ℕ) hc
      simpa only [ZMod.val_natCast] using hv
    apply Subtype.ext
    apply Fin.ext
    calc
      k.val.val = k.val.val % q + q * (k.val.val / q) := (Nat.mod_add_div _ _).symm
      _ = l.val.val % q + q * (l.val.val / q) := by rw [hm, hd]
      _ = l.val.val := Nat.mod_add_div _ _
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fin]
    using Fintype.card_le_of_injective f hf

noncomputable def reciprocalBlock (q U : ℕ) (r : ZMod q) : ℝ := by
  classical
  exact ∑ k : ResidueHits q U U r, 1 / ((U + k.val.val : ℕ) : ℝ)

/-- Every residue class in [U,2U) has reciprocal mass at most 2/q if q<=U.
No coprimality or statistical equidistribution hypothesis is present. -/
theorem reciprocalBlock_le (q U : ℕ) (hq : 0 < q) (hqU : q ≤ U) (r : ZMod q) :
    reciprocalBlock q U r ≤ 2 / (q : ℝ) := by
  classical
  have hU : 0 < U := lt_of_lt_of_le hq hqU
  have hUr : (0 : ℝ) < (U : ℝ) := by exact_mod_cast hU
  have hqr : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqUr : (q : ℝ) ≤ (U : ℝ) := by exact_mod_cast hqU
  have hcard : (Fintype.card (ResidueHits q U U r) : ℝ) ≤
      ((U / q : ℕ) : ℝ) + 1 := by
    have h := residueHits_card_le q U U hq r
    rw [Nat.card_eq_fintype_card] at h
    exact_mod_cast h
  have hdiv : ((U / q : ℕ) : ℝ) * (q : ℝ) ≤ (U : ℝ) := by
    exact_mod_cast Nat.div_mul_le_self U q
  calc
    reciprocalBlock q U r ≤
        ∑ _k : ResidueHits q U U r, (1 : ℝ) / (U : ℝ) := by
      unfold reciprocalBlock
      apply Finset.sum_le_sum
      intro k hk
      apply one_div_le_one_div_of_le hUr
      exact_mod_cast Nat.le_add_right U k.val.val
    _ = (Fintype.card (ResidueHits q U U r) : ℝ) / (U : ℝ) := by
      simp [div_eq_mul_inv]
    _ ≤ 2 / (q : ℝ) := by
      apply (div_le_div_iff₀ hUr hqr).2
      have hm := mul_le_mul_of_nonneg_right hcard hqr.le
      nlinarith

end Late
end PrimeAbundance
