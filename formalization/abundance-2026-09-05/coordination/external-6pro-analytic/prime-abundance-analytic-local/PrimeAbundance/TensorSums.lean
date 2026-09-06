/- Finite product sums and their first moments; no measure-theoretic input. -/
import PrimeAbundance.Sums

set_option autoImplicit false
open scoped Classical
open scoped BigOperators
open Finset

namespace PrimeAbundance.Analytic
noncomputable section

lemma sum_pi_product {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → κ → ℝ) :
    (∑ x : ι → κ, ∏ i : ι, f i (x i)) = ∏ i : ι, ∑ j : κ, f i j := by
  classical
  simpa using (Finset.sum_prod_piFinset (ι := ι) (univ : Finset κ) f)

lemma prod_at_mul_erase {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℝ) (p : ι) :
    (∏ i : ι, f i) = f p * ∏ i ∈ (univ : Finset ι).erase p, f i := by
  calc
    (∏ i : ι, f i) = ∏ i ∈ insert p ((univ : Finset ι).erase p), f i := by simp
    _ = f p * ∏ i ∈ (univ : Finset ι).erase p, f i := prod_insert (notMem_erase _ _)

lemma sum_pi_product_coordinate {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (f : ι → κ → ℝ) (g : κ → ℝ) (p : ι) :
    (∑ x : ι → κ, (∏ i : ι, f i (x i))*g (x p)) =
      (∑ a : κ, f p a*g a) *
        ∏ i ∈ (univ : Finset ι).erase p, ∑ a : κ, f i a := by
  classical
  let h : ι → κ → ℝ := fun i a => if i=p then f i a*g a else f i a
  have hp : ∀ x : ι → κ,
      (∏ i : ι, f i (x i))*g (x p) = ∏ i : ι, h i (x i) := by
    intro x
    rw [prod_at_mul_erase _ p, prod_at_mul_erase _ p]
    have hr : (∏ i ∈ (univ : Finset ι).erase p, h i (x i)) =
        ∏ i ∈ (univ : Finset ι).erase p, f i (x i) := by
      apply prod_congr rfl
      intro i hi
      simp [h, (mem_erase.mp hi).1]
    rw [hr]
    simp only [h, if_pos rfl]
    ring
  calc
    (∑ x : ι → κ, (∏ i : ι, f i (x i))*g (x p)) =
        ∑ x : ι → κ, ∏ i : ι, h i (x i) := sum_congr rfl (fun x _ => hp x)
    _ = ∏ i : ι, ∑ a : κ, h i a := by
      have hd : (inferInstance : DecidableEq ι) =
          (fun a b => Classical.propDecidable (a = b)) := Subsingleton.elim _ _
      simpa only [hd] using sum_pi_product h
    _ = _ := ?_
  rw [prod_at_mul_erase _ p]
  have hr : (∏ i ∈ (univ : Finset ι).erase p, ∑ a : κ, h i a) =
      ∏ i ∈ (univ : Finset ι).erase p, ∑ a : κ, f i a := by
    apply prod_congr rfl
    intro i hi
    simp [h, (mem_erase.mp hi).1]
  rw [hr]
  simp [h]

/-- A bound for one-coordinate expectations gives a bound for the sum of coordinates. -/
lemma product_weight_moment {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (f g : ι → κ → ℝ) (b : ι → ℝ)
    (hf : ∀ i a, 0 ≤ f i a)
    (hlocal : ∀ i, (∑ a : κ, f i a*g i a) ≤ b i*(∑ a : κ, f i a)) :
    (∑ x : ι → κ, (∏ i : ι, f i (x i))*(∑ i : ι, g i (x i))) ≤
      (∏ i : ι, ∑ a : κ, f i a) * ∑ i : ι, b i := by
  classical
  simp_rw [mul_sum]
  -- `simp_rw` has already distributed the right-hand product over its sum.
  rw [sum_comm]
  apply sum_le_sum
  intro i hi
  rw [sum_pi_product_coordinate f (g i) i, prod_at_mul_erase _ i]
  have hrest : 0 ≤ ∏ j ∈ (univ : Finset ι).erase i, ∑ a : κ, f j a := by
    exact prod_nonneg (fun j _ => sum_nonneg (fun a _ => hf j a))
  have h := mul_le_mul_of_nonneg_right (hlocal i) hrest
  nlinarith

lemma finite_geometric_identity (r : ℝ) (J : ℕ) :
    (1-r)*(∑ j ∈ range (J+1), r^j) = 1-r^(J+1) := by
  induction J with
  | zero => simp
  | succ J ih =>
    -- Expand only the new endpoint, not the shorter sum in the induction hypothesis.
    rw [sum_range_succ (fun j : ℕ => r^j) (J+1), mul_add, ih]
    rw [pow_succ r (J+1)]
    ring

lemma finite_geometric_moment_identity (r : ℝ) (J : ℕ) :
    (1-r)*(∑ j ∈ range (J+1), (j:ℝ)*r^j) =
      r*(∑ j ∈ range (J+1), r^j) - ((J+1:ℕ):ℝ)*r^(J+1) := by
  induction J with
  | zero => simp
  | succ J ih =>
    -- The summands differ. Specify both, so the second rewrite cannot
    -- expand the shorter weighted sum again.
    rw [sum_range_succ (fun j : ℕ => (j:ℝ)*r^j) (J+1),
      sum_range_succ (fun j : ℕ => r^j) (J+1), mul_add, ih]
    rw [pow_succ r (J+1)]
    push_cast
    ring

lemma finite_geometric_moment_le (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (J : ℕ) :
    (∑ j : Fin (J+1), (r^j.val)*(j.val:ℝ)) ≤
      (r/(1-r))*(∑ j : Fin (J+1), r^j.val) := by
  rw [Fin.sum_univ_eq_sum_range (fun j => r^j*(j:ℝ)),
    Fin.sum_univ_eq_sum_range (fun j => r^j)]
  have h := finite_geometric_moment_identity r J
  have hlast : 0 ≤ ((J+1:ℕ):ℝ)*r^(J+1) := by positivity
  have hreorder : (r/(1-r))*(∑ j ∈ range (J+1), r^j) =
      (r*(∑ j ∈ range (J+1), r^j))/(1-r) := by ring
  rw [hreorder]
  apply (le_div_iff₀ (sub_pos.mpr hr1)).mpr
  -- Commute the two factors in the summands before clearing the positive denominator.
  have hs : (∑ j ∈ range (J+1), r^j*(j:ℝ)) =
      ∑ j ∈ range (J+1), (j:ℝ)*r^j := by
    apply sum_congr rfl
    intro j hj
    ring
  rw [hs]
  nlinarith

/-- Finite Markov splitting, with no probabilistic normalization. -/
lemma finite_weight_low_mass {Ω : Type*} [Fintype Ω]
    (weight height : Ω → ℝ) (T : ℝ) (hT : 0 < T)
    (hw : ∀ x, 0 ≤ weight x) (hh : ∀ x, 0 ≤ height x)
    (hmean : (∑ x : Ω, weight x*height x) ≤ (T/2)*(∑ x : Ω, weight x)) :
    (∑ x : Ω, weight x) ≤ 2*(∑ x ∈ (univ : Finset Ω).filter (fun x => height x≤T), weight x) := by
  classical
  let lo := (univ : Finset Ω).filter (fun x => height x≤T)
  let hi := (univ : Finset Ω).filter (fun x => T<height x)
  have hsplit : (∑ x : Ω, weight x) = (∑ x ∈ lo, weight x)+(∑ x ∈ hi, weight x) := by
    dsimp [lo, hi]
    rw [sum_filter, sum_filter, ← sum_add_distrib]
    apply sum_congr rfl
    intro x hx
    by_cases h : height x≤T
    · simp [h, not_lt.mpr h]
    · simp [h, lt_of_not_ge h]
  have hhigh : T*(∑ x ∈ hi, weight x) ≤ ∑ x : Ω, weight x*height x := by
    calc
      T*(∑ x ∈ hi, weight x) ≤ ∑ x ∈ hi, weight x*height x := by
        rw [mul_sum]
        apply sum_le_sum
        intro x hx
        have ht := (mem_filter.mp hx).2.le
        nlinarith [mul_le_mul_of_nonneg_left ht (hw x)]
      _ ≤ ∑ x : Ω, weight x*height x :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          (fun x _ _ => mul_nonneg (hw x) (hh x))
  nlinarith

end
end PrimeAbundance.Analytic
