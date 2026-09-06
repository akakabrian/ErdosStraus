/-
Finite real sums used by the analytic argument.
Source candidate for Lean/mathlib 4.27.0. Not compiled in this conversation.
-/
import Mathlib

set_option autoImplicit false
open scoped Classical
open scoped BigOperators
open Finset

namespace PrimeAbundance.Analytic

noncomputable section

/-- Move the innermost of three independent finite sums to the outside.
The three index types need not agree; confusing a scale index with a divisor
index cannot be hidden by using the same ambient type. -/
lemma sum_rotate_three {α β γ : Type*}
    (s : Finset α) (t : Finset β) (u : Finset γ) (f : α → β → γ → ℝ) :
    (∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, f a b c) =
      ∑ c ∈ u, ∑ a ∈ s, ∑ b ∈ t, f a b c := by
  calc
    (∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, f a b c) =
        ∑ a ∈ s, ∑ c ∈ u, ∑ b ∈ t, f a b c := by
      apply sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = ∑ c ∈ u, ∑ a ∈ s, ∑ b ∈ t, f a b c := by
      rw [Finset.sum_comm]

/-- The real harmonic sum, with the zero summand excluded. -/
def H (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, 1 / (n : ℝ)

lemma H_eq_harmonic (N : ℕ) : H N = (harmonic N : ℝ) := by
  simp only [H, harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
    Rat.cast_natCast, one_div]

lemma H_nonneg (N : ℕ) : 0 ≤ H N := by
  exact sum_nonneg (fun _ _ => by positivity)

lemma H_mono : Monotone H := by
  intro m n hmn
  exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl hmn)
    (fun _ _ _ => by positivity)

lemma H_le (N : ℕ) : H N ≤ 1 + Real.log (N : ℝ) := by
  rw [H_eq_harmonic]
  exact harmonic_le_one_add_log N

lemma log_le_H (N : ℕ) (hN : 0 < N) : Real.log (N : ℝ) ≤ H N := by
  rw [H_eq_harmonic]
  exact (Real.log_le_log (by exact_mod_cast hN)
    (by exact_mod_cast Nat.le_succ N)).trans (log_add_one_le_harmonic N)

lemma H_one : H 1 = 1 := by norm_num [H]
lemma H_ge_one (N : ℕ) (hN : 0 < N) : 1 ≤ H N := by
  rw [← H_one]
  exact H_mono hN

lemma inv_nat_nonneg (n : ℕ) : 0 ≤ 1 / (n : ℝ) := by positivity

/-- The only cubic-moment inequality needed; no analytic Hölder theorem is used. -/
lemma three_mul_le_cubes (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    3 * (x * y * z) ≤ x ^ 3 + y ^ 3 + z ^ 3 := by
  have h := mul_nonneg (add_nonneg (add_nonneg hx hy) hz)
    (add_nonneg (add_nonneg (sq_nonneg (x-y)) (sq_nonneg (y-z)))
      (sq_nonneg (z-x)))
  nlinarith [h]

lemma sum_three_mul_le_cubes {α : Type*} (s : Finset α) (f g h : α → ℝ)
    (hf : ∀ a ∈ s, 0 ≤ f a) (hg : ∀ a ∈ s, 0 ≤ g a)
    (hh : ∀ a ∈ s, 0 ≤ h a) :
    3 * (∑ a ∈ s, f a * g a * h a) ≤
      (∑ a ∈ s, f a ^ 3) + (∑ a ∈ s, g a ^ 3) + (∑ a ∈ s, h a ^ 3) := by
  simpa only [mul_sum, sum_add_distrib] using
    sum_le_sum (fun a ha => three_mul_le_cubes (f a) (g a) (h a)
      (hf a ha) (hg a ha) (hh a ha))

/-- A positive finite cover may overcount. -/
lemma sum_le_sum_of_cover {α β : Type*} [DecidableEq α]
    (s : Finset α) (t : Finset β) (u : β → Finset α) (f : α → ℝ)
    (hf : ∀ a, 0 ≤ f a) (hcover : ∀ a ∈ s, ∃ b ∈ t, a ∈ u b) :
    ∑ a ∈ s, f a ≤ ∑ b ∈ t, ∑ a ∈ u b, f a := by
  classical
  calc
    ∑ a ∈ s, f a ≤ ∑ a ∈ s, ∑ b ∈ t, if a ∈ u b then f a else 0 := by
      apply sum_le_sum
      intro a ha
      obtain ⟨b, hb, hab⟩ := hcover a ha
      calc
        f a = (if a ∈ u b then f a else 0) := by simp [hab]
        _ ≤ ∑ c ∈ t, if a ∈ u c then f a else 0 :=
          single_le_sum (f := fun c => if a ∈ u c then f a else 0)
            (fun c _ => by dsimp; split_ifs; exact hf a; exact le_rfl) hb
    _ = ∑ b ∈ t, ∑ a ∈ s, if a ∈ u b then f a else 0 := by rw [sum_comm]
    _ ≤ ∑ b ∈ t, ∑ a ∈ u b, f a := by
      apply sum_le_sum
      intro b hb
      rw [← sum_filter]
      exact sum_le_sum_of_subset_of_nonneg
        (fun a ha => (mem_filter.mp ha).2) (fun a _ _ => hf a)

/-- A weighted map into a finite set, with at most C points per fiber. -/
lemma sum_le_mul_sum_of_fiber_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (f : α → β) (w : β → ℝ) (C : ℕ)
    (hmap : ∀ a ∈ s, f a ∈ t)
    (hcard : ∀ b ∈ t, (s.filter (fun a => f a = b)).card ≤ C)
    (hw : ∀ b ∈ t, 0 ≤ w b) :
    ∑ a ∈ s, w (f a) ≤ (C : ℝ) * ∑ b ∈ t, w b := by
  classical
  have hsplit : (∑ a ∈ s, w (f a)) =
      ∑ b ∈ t, ∑ a ∈ s, if f a = b then w b else 0 := by
    rw [sum_comm]
    apply sum_congr rfl
    intro a ha
    simp [hmap a ha]
  rw [hsplit, mul_sum]
  apply sum_le_sum
  intro b hb
  rw [← sum_filter, sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard b hb) (hw b hb)

/-- Weighted injection: the codomain sum includes every image once. -/
lemma sum_le_sum_of_injOn {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (f : α → β) (w : β → ℝ)
    (hmap : ∀ a ∈ s, f a ∈ t) (hinj : Set.InjOn f s)
    (hw : ∀ b ∈ t, 0 ≤ w b) :
    ∑ a ∈ s, w (f a) ≤ ∑ b ∈ t, w b := by
  classical
  rw [← sum_image (fun a ha b hb h => hinj ha hb h)]
  exact sum_le_sum_of_subset_of_nonneg
    (by intro b hb; obtain ⟨a, ha, rfl⟩ := mem_image.mp hb; exact hmap a ha)
    (fun b hb _ => hw b hb)

/-- Product monotonicity under adding factors at least one. -/
lemma product_mono_subset {α : Type*} [DecidableEq α]
    (s t : Finset α) (f : α → ℝ) (hst : s ⊆ t)
    (hf : ∀ a ∈ t, 1 ≤ f a) :
    (∏ a ∈ s, f a) ≤ ∏ a ∈ t, f a := by
  have hu : s ∪ (t \ s) = t := union_sdiff_of_subset hst
  have hd : Disjoint s (t \ s) := disjoint_left.mpr
    (fun a ha hb => (mem_sdiff.mp hb).2 ha)
  have hp0 : 0 ≤ ∏ a ∈ s, f a :=
    prod_nonneg (fun a ha => (by linarith [hf a (hst ha)]))
  have hp1 : (1:ℝ) ≤ ∏ a ∈ t \ s, f a := by
    have h := prod_le_prod (s := t \ s) (f := fun _ => (1:ℝ))
      (g := f) (fun _ _ => by norm_num)
      (fun a ha => hf a (mem_sdiff.mp ha).1)
    simpa using h
  conv_rhs => rw [← hu, prod_union hd]
  nlinarith

/-- Product antitonicity under adding factors in [0,1]. -/
lemma product_antitone_subset {α : Type*} [DecidableEq α]
    (s t : Finset α) (f : α → ℝ) (hst : s ⊆ t)
    (hf0 : ∀ a ∈ t, 0 ≤ f a) (hf1 : ∀ a ∈ t, f a ≤ 1) :
    (∏ a ∈ t, f a) ≤ ∏ a ∈ s, f a := by
  have hu : s ∪ (t \ s) = t := union_sdiff_of_subset hst
  have hd : Disjoint s (t \ s) := disjoint_left.mpr
    (fun a ha hb => (mem_sdiff.mp hb).2 ha)
  have hp0 : 0 ≤ ∏ a ∈ s, f a := prod_nonneg (fun a ha => hf0 a (hst ha))
  have hp1 : (∏ a ∈ t \ s, f a) ≤ (1:ℝ) :=
    prod_le_one (fun a ha => hf0 a (mem_sdiff.mp ha).1)
      (fun a ha => hf1 a (mem_sdiff.mp ha).1)
  conv_lhs => rw [← hu, prod_union hd]
  nlinarith

/-- Squared reciprocal tail, by the telescoping comparison 1/n² ≤ 1/(n-1)-1/n. -/
lemma reciprocal_sq_tail (K N : ℕ) (hK : 2 ≤ K) :
    (∑ n ∈ Icc K N, 1 / (n : ℝ) ^ 2) ≤ 1 / ((K-1 : ℕ) : ℝ) := by
  by_cases hKN : K ≤ N
  · have htel : ∀ m : ℕ,
        (∑ j ∈ range m, 1 / ((K+j : ℕ) : ℝ) ^ 2) ≤
          1 / ((K-1 : ℕ) : ℝ) - 1 / ((K+m-1 : ℕ) : ℝ) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [sum_range_succ]
        have hn : (1 : ℝ) < ((K+m : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < K+m)
        have hprev : ((K+m-1 : ℕ) : ℝ) = ((K+m : ℕ) : ℝ)-1 := by
          rw [Nat.cast_sub (by omega), Nat.cast_one]
        have hnext : K+(m+1)-1=K+m := by omega
        rw [hnext]
        have ht : 1 / ((K+m : ℕ) : ℝ)^2 ≤
            1 / ((K+m-1 : ℕ) : ℝ) - 1 / ((K+m : ℕ) : ℝ) := by
          rw [hprev]
          have hpos : 0 < ((K+m : ℕ) : ℝ)-1 := by linarith
          field_simp
          nlinarith
        linarith
    have hrewrite : (∑ n ∈ Icc K N, 1 / (n : ℝ)^2) =
        ∑ j ∈ range (N+1-K), 1 / ((K+j : ℕ) : ℝ)^2 := by
      refine sum_bij (fun n _ => n-K) ?_ ?_ ?_ ?_
      · intro n hn
        simp only [mem_Icc] at hn
        simp only [mem_range]
        omega
      · intro n hn m hm h
        dsimp at h
        simp only [mem_Icc] at hn hm
        omega
      · intro j hj
        refine ⟨K+j, ?_, ?_⟩
        · simp only [mem_Icc, mem_range] at *
          omega
        · dsimp
          omega
      · intro n hn
        have hnK := (mem_Icc.mp hn).1
        have he : K+(n-K)=n := by omega
        rw [he]
    rw [hrewrite]
    exact (htel _).trans (sub_le_self _ (by positivity))
  · simp [Icc_eq_empty_of_lt (lt_of_not_ge hKN)]

lemma reciprocal_sq_sum_le_two (N : ℕ) :
    (∑ n ∈ Icc 1 N, 1 / (n : ℝ)^2) ≤ 2 := by
  by_cases hN : 1 ≤ N
  · -- A disjoint split at 1 avoids any assertion about the empty interval.
    have hs : (∑ n ∈ Icc 1 N, 1 / (n : ℝ)^2) =
        1 + ∑ n ∈ Icc 2 N, 1 / (n : ℝ)^2 := by
      rw [← sum_erase_add _ _ (left_mem_Icc.mpr hN)]
      have hi : Ioc 1 N = Icc 2 N := by ext n; simp; omega
      simp [Icc_erase_left, hi, add_comm]
    rw [hs]
    have ht := reciprocal_sq_tail 2 N (by decide)
    norm_num only [Nat.cast_ofNat, sub_self, sub_zero, one_div_one] at ht
    linarith
  · have : N=0 := by omega
    simp [this]

/-- The j-th positive dyadic block. -/
def dyadicBlock (j : ℕ) : Finset ℕ := Ico (2^j) (2^(j+1))

lemma dyadicBlock_pos {j m : ℕ} (hm : m ∈ dyadicBlock j) : 0 < m := by
  exact lt_of_lt_of_le (by positivity : 0 < 2^j) (mem_Ico.mp hm).1

lemma dyadicBlock_card (j : ℕ) : (dyadicBlock j).card = 2^j := by
  simp only [dyadicBlock, Nat.card_Ico, pow_succ]
  omega

lemma mem_dyadicBlock_log {m : ℕ} (hm : 0 < m) :
    m ∈ dyadicBlock (Nat.log 2 m) := by
  exact mem_Ico.mpr ⟨Nat.pow_log_le_self 2 hm.ne',
    Nat.lt_pow_succ_log_self (by decide) m⟩

lemma dyadicBlock_log_lt {m J : ℕ} (hm : 0 < m) (hJ : m < 2^J) :
    Nat.log 2 m < J :=
  (Nat.log_lt_iff_lt_pow (by decide) hm.ne').mpr hJ

lemma sum_Icc_le_dyadic (f : ℕ → ℝ) (hf : ∀ m, 0 ≤ f m) (N J : ℕ)
    (hNJ : N < 2^J) :
    ∑ m ∈ Icc 1 N, f m ≤ ∑ j ∈ range J, ∑ m ∈ dyadicBlock j, f m := by
  apply sum_le_sum_of_cover _ _ _ _ hf
  intro m hm
  obtain ⟨hm1, hmN⟩ := mem_Icc.mp hm
  refine ⟨Nat.log 2 m, ?_, mem_dyadicBlock_log hm1⟩
  exact mem_range.mpr (dyadicBlock_log_lt hm1 (lt_of_le_of_lt hmN hNJ))

/-- Growth/decay manipulations later use this elementary bound for ceil log₂. -/
lemma log_two_nat_le_real (n : ℕ) (hn : 0 < n) :
    (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log (n : ℝ) := by
  have hp := Nat.pow_log_le_self 2 hn.ne'
  have hpR : (2:ℝ) ^ Nat.log 2 n ≤ (n:ℝ) := by exact_mod_cast hp
  have ht := Real.log_le_log (by positivity : (0:ℝ) < (2:ℝ)^(Nat.log 2 n)) hpR
  simpa only [Real.log_pow] using ht

lemma real_log_nat_lt (n : ℕ) (hn : 0 < n) :
    Real.log (n : ℝ) < ((Nat.log 2 n : ℝ)+1)*Real.log 2 := by
  have hp := Nat.lt_pow_succ_log_self (b := 2) (by decide) n
  have hpR : (n:ℝ) < (2:ℝ) ^ (Nat.log 2 n + 1) := by exact_mod_cast hp
  have ht := Real.log_lt_log (by exact_mod_cast hn : (0:ℝ) < (n:ℝ)) hpR
  simpa only [Real.log_pow, Nat.cast_add, Nat.cast_one] using ht

end
end PrimeAbundance.Analytic
