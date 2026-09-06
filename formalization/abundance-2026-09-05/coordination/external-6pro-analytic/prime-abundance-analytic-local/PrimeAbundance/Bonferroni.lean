/-
Finite Bonferroni inequalities and a geometric, rather than factorial, remainder.
Every object in this module is a finite sum or product. No sieve estimate is assumed.
Uncompiled proof-source candidate, Lean/mathlib 4.27.0.
-/
import PrimeAbundance.Sums

set_option autoImplicit false
open scoped Classical
open scoped BigOperators
open Finset

namespace PrimeAbundance.Analytic
noncomputable section

variable {α : Type*} [DecidableEq α]

/-- Signed inclusion-exclusion truncated after subsets of size k. -/
def truncation (s : Finset α) (x : α → ℝ) (k : ℕ) : ℝ :=
  ∑ t ∈ s.powerset, if t.card ≤ k then (-1 : ℝ)^t.card * ∏ a ∈ t, x a else 0

def productComplement (s : Finset α) (x : α → ℝ) : ℝ := ∏ a ∈ s, (1-x a)

lemma truncation_zero (s : Finset α) (x : α → ℝ) : truncation s x 0 = 1 := by
  simp [truncation, Nat.le_zero, card_eq_zero]

lemma truncation_empty (x : α → ℝ) (k : ℕ) : truncation (∅ : Finset α) x k = 1 := by
  simp [truncation]

lemma truncation_insert (s : Finset α) (a : α) (ha : a ∉ s)
    (x : α → ℝ) (k : ℕ) :
    truncation (insert a s) x (k+1) =
      truncation s x (k+1) - x a * truncation s x k := by
  rw [truncation, sum_powerset_insert ha]
  change truncation s x (k+1) + _ = _
  rw [sub_eq_add_neg]
  congr 1
  rw [truncation, mul_sum, ← sum_neg_distrib]
  apply sum_congr rfl
  intro t ht
  have hat : a ∉ t := fun h => ha ((mem_powerset.mp ht) h)
  simp only [card_insert_of_notMem hat, prod_insert hat, Nat.add_le_add_iff_right,
    pow_succ]
  by_cases h : t.card ≤ k <;> simp [h] <;> ring

lemma productComplement_nonneg (s : Finset α) (x : α → ℝ)
    (hx : ∀ a ∈ s, x a ≤ 1) : 0 ≤ productComplement s x := by
  apply prod_nonneg
  intro a ha
  exact sub_nonneg.mpr (hx a ha)

lemma productComplement_le_one (s : Finset α) (x : α → ℝ)
    (hx0 : ∀ a ∈ s, 0 ≤ x a) (hx1 : ∀ a ∈ s, x a ≤ 1) :
    productComplement s x ≤ 1 := by
  unfold productComplement
  exact prod_le_one (fun a ha => sub_nonneg.mpr (hx1 a ha))
    (fun a ha => sub_le_self _ (hx0 a ha))

/-- The sign of each truncation error. Even truncations are upper bounds. -/
theorem bonferroni (s : Finset α) (x : α → ℝ)
    (hx0 : ∀ a ∈ s, 0 ≤ x a) (hx1 : ∀ a ∈ s, x a ≤ 1) (k : ℕ) :
    0 ≤ (-1 : ℝ)^k * (truncation s x k - productComplement s x) := by
  induction s using Finset.induction_on generalizing k with
  | empty => simp [truncation_empty, productComplement]
  | @insert a s ha ih =>
    have ha0 := hx0 a (mem_insert_self _ _)
    have ha1 := hx1 a (mem_insert_self _ _)
    have hs0 : ∀ b ∈ s, 0 ≤ x b := fun b hb => hx0 b (mem_insert_of_mem hb)
    have hs1 : ∀ b ∈ s, x b ≤ 1 := fun b hb => hx1 b (mem_insert_of_mem hb)
    cases k with
    | zero =>
      simpa only [pow_zero, one_mul, truncation_zero] using
        sub_nonneg.mpr (productComplement_le_one (insert a s) x hx0 hx1)
    | succ k =>
      have h0 := ih hs0 hs1 k
      have h1 := ih hs0 hs1 (k+1)
      rw [truncation_insert s a ha x k]
      have hp : productComplement (insert a s) x =
          (1-x a)*productComplement s x := by simp [productComplement, ha]
      rw [hp]
      have hid : (-1 : ℝ)^(k+1) *
          (truncation s x (k+1) - x a*truncation s x k -
            (1-x a)*productComplement s x) =
          (-1 : ℝ)^(k+1)*(truncation s x (k+1)-productComplement s x) +
          x a*((-1 : ℝ)^k*(truncation s x k-productComplement s x)) := by
        rw [pow_succ]
        ring
      rw [hid]
      exact add_nonneg h1 (mul_nonneg ha0 h0)

lemma powerset_product_expansion (s : Finset α) (x : α → ℝ) :
    (∑ t ∈ s.powerset, ∏ a ∈ t, x a) = ∏ a ∈ s, (1+x a) := by
  exact (Finset.prod_one_add (f := x) s).symm

lemma signed_powerset_expansion (s : Finset α) (x : α → ℝ) :
    (∑ t ∈ s.powerset, (-1 : ℝ)^t.card * ∏ a ∈ t, x a) =
      productComplement s x := by
  have h := powerset_product_expansion s (fun a => -x a)
  simpa only [prod_neg, sub_eq_add_neg] using h

lemma truncation_error_eq (s : Finset α) (x : α → ℝ) (k : ℕ) :
    truncation s x k - productComplement s x =
      -(∑ t ∈ s.powerset, if k < t.card then
        (-1 : ℝ)^t.card * ∏ a ∈ t, x a else 0) := by
  rw [← signed_powerset_expansion, truncation, ← sum_sub_distrib, ← sum_neg_distrib]
  apply sum_congr rfl
  intro t ht
  by_cases h : t.card ≤ k
  · simp [h, not_lt.mpr h]
  · simp [h, lt_of_not_ge h]

/-- The high-degree tail is bounded by the same product with doubled weights. -/
theorem truncation_error_le_geometric (s : Finset α) (x : α → ℝ)
    (hx : ∀ a ∈ s, 0 ≤ x a) (k : ℕ) :
    |truncation s x k - productComplement s x| ≤
      (∏ a ∈ s, (1+2*x a)) / (2 : ℝ)^(k+1) := by
  have hpow : 0 < (2 : ℝ)^(k+1) := by positivity
  rw [le_div_iff₀ hpow, truncation_error_eq, abs_neg]
  calc
    |∑ t ∈ s.powerset, if k < t.card then
        (-1 : ℝ)^t.card * ∏ a ∈ t, x a else 0| * 2^(k+1)
        ≤ (∑ t ∈ s.powerset, |if k < t.card then
          (-1 : ℝ)^t.card * ∏ a ∈ t, x a else 0|) * 2^(k+1) :=
          mul_le_mul_of_nonneg_right (abs_sum_le_sum_abs _ _) hpow.le
    _ ≤ ∑ t ∈ s.powerset, ∏ a ∈ t, (2*x a) := by
      rw [sum_mul]
      apply sum_le_sum
      intro t ht
      have ht0 : 0 ≤ ∏ a ∈ t, x a :=
        prod_nonneg (fun a ha => hx a ((mem_powerset.mp ht) ha))
      by_cases hk : k < t.card
      · simp only [if_pos hk, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
          abs_of_nonneg ht0, prod_mul_distrib, prod_const]
        have he : (2 : ℝ)^(k+1) ≤ 2^t.card :=
          pow_le_pow_right₀ (by norm_num) hk
        nlinarith
      · simp only [if_neg hk, abs_zero, zero_mul]
        exact prod_nonneg (fun a ha => mul_nonneg (by norm_num)
          (hx a ((mem_powerset.mp ht) ha)))
    _ = ∏ a ∈ s, (1+2*x a) := powerset_product_expansion s _

/-- Weighted finite union bound in multiplicative form. -/
lemma one_sub_sum_le_product (s : Finset α) (x : α → ℝ)
    (hx0 : ∀ a ∈ s, 0 ≤ x a) (hx1 : ∀ a ∈ s, x a ≤ 1) :
    1 - ∑ a ∈ s, x a ≤ productComplement s x := by
  induction s using Finset.induction_on with
  | empty => simp [productComplement]
  | @insert a s ha ih =>
    have h0 := hx0 a (mem_insert_self _ _)
    have h1 := hx1 a (mem_insert_self _ _)
    have hs0 : ∀ b ∈ s, 0 ≤ x b := fun b hb => hx0 b (mem_insert_of_mem hb)
    have hs1 : ∀ b ∈ s, x b ≤ 1 := fun b hb => hx1 b (mem_insert_of_mem hb)
    have hi := ih hs0 hs1
    have hs := sum_nonneg hs0
    have hp := mul_le_mul_of_nonneg_left hi (sub_nonneg.mpr h1)
    simp only [sum_insert ha, productComplement, prod_insert ha] at *
    nlinarith

/-- An event indicator as a real number. -/
def indicator (P : Prop) [Decidable P] : ℝ := if P then 1 else 0

lemma indicator_nonneg (P : Prop) [Decidable P] : 0 ≤ indicator P := by
  unfold indicator
  split_ifs <;> norm_num

lemma indicator_le_one (P : Prop) [Decidable P] : indicator P ≤ 1 := by
  unfold indicator
  split_ifs <;> norm_num

lemma prod_indicator (s : Finset α) (P : α → Prop) [DecidablePred P] :
    (∏ a ∈ s, indicator (P a)) = indicator (∀ a ∈ s, P a) := by
  induction s using Finset.induction_on with
  | empty => simp [indicator]
  | @insert a s ha ih =>
    simp only [prod_insert ha, ih, mem_insert, forall_eq_or_imp]
    by_cases h : P a <;> by_cases h' : ∀ b ∈ s, P b <;> simp [indicator, h, h']

lemma productComplement_indicator (s : Finset α) (P : α → Prop) [DecidablePred P] :
    productComplement s (fun a => indicator (P a)) =
      indicator (∀ a ∈ s, ¬P a) := by
  unfold productComplement
  have h : ∀ a, 1-indicator (P a) = indicator (¬P a) := by
    intro a
    by_cases ha : P a <;> simp [indicator, ha]
  simp_rw [h]
  exact prod_indicator s (fun a => ¬P a)

/-- The analytic input for a finite Bonferroni estimate is only the individual
intersection counting error, not a sieve conclusion. -/
theorem finite_bonferroni_count
    {Ω : Type*} [Fintype Ω] (s : Finset α) (P : α → Ω → Prop)
    [∀ a, DecidablePred (P a)] (x : α → ℝ) (H E : ℝ) (k : ℕ)
    (hH : 0 ≤ H) (hE : 0 ≤ E)
    (hx0 : ∀ a ∈ s, 0 ≤ x a) (hx1 : ∀ a ∈ s, x a ≤ 1)
    (hk : Even k)
    (hcount : ∀ t ∈ s.powerset, t.card ≤ k+1 →
      |(∑ ω : Ω, indicator (∀ a ∈ t, P a ω)) - H*(∏ a ∈ t, x a)| ≤ 1)
    (hsize : ∀ j ≤ k+1, (((s.powerset).filter (fun t => t.card ≤ j)).card : ℝ) ≤ E) :
    |(∑ ω : Ω, indicator (∀ a ∈ s, ¬P a ω)) -
        H*productComplement s x| ≤
      E + H * ((∏ a ∈ s, (1+2*x a))/(2:ℝ)^(k+1)) := by
  classical
  let A : ℕ → ℝ := fun j =>
    ∑ ω : Ω, truncation s (fun a => indicator (P a ω)) j
  let S : ℝ := ∑ ω : Ω, indicator (∀ a ∈ s, ¬P a ω)
  have hlin : ∀ j ≤ k+1, |A j - H*truncation s x j| ≤ E := by
    intro j hj
    have hid : A j - H*truncation s x j =
        ∑ t ∈ (s.powerset).filter (fun t => t.card ≤ j),
          (-1:ℝ)^t.card *
            ((∑ ω : Ω, indicator (∀ a ∈ t, P a ω))-H*(∏ a ∈ t, x a)) := by
      dsimp [A]
      simp_rw [truncation, ← sum_filter, ← prod_indicator]
      rw [sum_comm, mul_sum, ← sum_sub_distrib]
      apply sum_congr rfl
      intro t ht
      rw [← mul_sum]
      ring
    rw [hid]
    calc
      |∑ t ∈ (s.powerset).filter (fun t => t.card ≤ j),
          (-1:ℝ)^t.card *
            ((∑ ω : Ω, indicator (∀ a ∈ t, P a ω))-H*(∏ a ∈ t, x a))|
          ≤ ∑ t ∈ (s.powerset).filter (fun t => t.card ≤ j),
            |(-1:ℝ)^t.card *
              ((∑ ω : Ω, indicator (∀ a ∈ t, P a ω))-H*(∏ a ∈ t, x a))| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ _t ∈ (s.powerset).filter (fun t => t.card ≤ j), (1:ℝ) := by
        apply sum_le_sum
        intro t ht
        obtain ⟨hts, htj⟩ := mem_filter.mp ht
        simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using
          hcount t hts (htj.trans hj)
      _ ≤ E := by simpa using hsize j hj
  have hupper : S ≤ A k := by
    apply sum_le_sum
    intro ω hω
    have h := bonferroni s (fun a => indicator (P a ω))
      (fun a _ => indicator_nonneg _) (fun a _ => indicator_le_one _) k
    have hsign : (-1:ℝ)^k = 1 := hk.neg_one_pow
    rw [hsign, one_mul, productComplement_indicator] at h
    exact sub_nonneg.mp h
  have hlower : A (k+1) ≤ S := by
    apply sum_le_sum
    intro ω hω
    have h := bonferroni s (fun a => indicator (P a ω))
      (fun a _ => indicator_nonneg _) (fun a _ => indicator_le_one _) (k+1)
    have hsign : (-1:ℝ)^(k+1) = -1 := by rw [pow_succ, hk.neg_one_pow]; norm_num
    rw [hsign, productComplement_indicator] at h
    linarith
  have htk := truncation_error_le_geometric s x hx0 k
  have htk1 := truncation_error_le_geometric s x hx0 (k+1)
  have hpow : (2:ℝ)^(k+1) ≤ 2^(k+1+1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hprod : 0 ≤ ∏ a ∈ s, (1+2*x a) := by
    apply prod_nonneg
    intro a ha
    nlinarith [hx0 a ha]
  have htk1' : |truncation s x (k+1)-productComplement s x| ≤
      (∏ a ∈ s, (1+2*x a))/(2:ℝ)^(k+1) :=
    htk1.trans (div_le_div_of_nonneg_left hprod (by positivity) hpow)
  have h0 := abs_le.mp (hlin k (by omega))
  have h1 := abs_le.mp (hlin (k+1) le_rfl)
  have ht0 := abs_le.mp htk
  have ht1 := abs_le.mp htk1'
  have hmul0 := mul_le_mul_of_nonneg_left ht0.2 hH
  have hmul1 := mul_le_mul_of_nonneg_left ht1.1 hH
  change |S-H*productComplement s x| ≤ _
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

end
end PrimeAbundance.Analytic
