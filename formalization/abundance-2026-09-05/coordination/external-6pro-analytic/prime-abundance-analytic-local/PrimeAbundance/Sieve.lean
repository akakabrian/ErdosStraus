/-
A finite, coefficient-uniform lower sieve. Its long-interval hypothesis is literal.
The cutoff is not treated as independent of the length in the eventual application.
Uncompiled source candidate for Lean/mathlib 4.27.0.
-/
import PrimeAbundance.Residues

set_option autoImplicit false
open scoped Classical
open scoped BigOperators
open Finset

namespace PrimeAbundance.Analytic
noncomputable section

def smallPrimes (w : ℕ) : Finset ℕ := (Icc 2 w).filter Nat.Prime

def activePrimes (c w : ℕ) : Finset ℕ := (smallPrimes w).filter (fun p => ¬p∣c)

def V (w : ℕ) : ℝ := ∏ p ∈ smallPrimes w, (1-1/(p:ℝ))

def Vcoeff (c w : ℕ) : ℝ := ∏ p ∈ activePrimes c w, (1-1/(p:ℝ))

def sieveLevel (w : ℕ) : ℕ := 8 * (Nat.log 2 w + 1)

def sieveLength (w : ℕ) : ℕ := 4 * w^(sieveLevel w + 2)

def roughScales (c U H w : ℕ) : Finset ℕ :=
  (Ioc U (U+H)).filter (fun m => w < Nat.minFac (c*m-1))

lemma mem_smallPrimes {w p : ℕ} :
    p ∈ smallPrimes w ↔ Nat.Prime p ∧ p≤w := by
  simp only [smallPrimes, mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨_, hpw⟩, hp⟩
    exact ⟨hp, hpw⟩
  · rintro ⟨hp, hpw⟩
    exact ⟨⟨hp.two_le, hpw⟩, hp⟩

lemma mem_activePrimes {c w p : ℕ} :
    p ∈ activePrimes c w ↔ Nat.Prime p ∧ p≤w ∧ ¬p∣c := by
  simp only [activePrimes, mem_filter, mem_smallPrimes, and_assoc]

lemma V_pos (w : ℕ) : 0 < V w := by
  apply prod_pos
  intro p hp
  have hpR : (1:ℝ)<(p:ℝ) := by exact_mod_cast (mem_smallPrimes.mp hp).1.one_lt
  have hinv : 1/(p:ℝ)<1 := (div_lt_one (by linarith)).mpr hpR
  linarith

lemma V_le_one (w : ℕ) : V w ≤ 1 := by
  apply prod_le_one
  · intro p hp
    have hpR : (1:ℝ)≤(p:ℝ) := by exact_mod_cast (mem_smallPrimes.mp hp).1.one_le
    exact sub_nonneg.mpr ((div_le_one (by linarith)).mpr hpR)
  · intro p hp
    exact sub_le_self _ (by positivity)

lemma V_le_Vcoeff (c w : ℕ) : V w ≤ Vcoeff c w := by
  apply product_antitone_subset (activePrimes c w) (smallPrimes w)
    (fun p => 1-1/(p:ℝ)) (filter_subset _ _)
  · intro p hp
    have hpR : (1:ℝ)≤(p:ℝ) := by exact_mod_cast (mem_smallPrimes.mp hp).1.one_le
    exact sub_nonneg.mpr ((div_le_one (by linarith)).mpr hpR)
  · intro p hp
    exact sub_le_self _ (by positivity)

lemma Vcoeff_pos (c w : ℕ) : 0 < Vcoeff c w :=
  lt_of_lt_of_le (V_pos w) (V_le_Vcoeff c w)

/-- Product over all integers, used only as a crude lower bound. -/
lemma telescoping_complement (n : ℕ) :
    (∏ m ∈ Icc 2 (n+1), (1-1/(m:ℝ))) = 1/((n+1:ℕ):ℝ) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hs : Icc 2 (n+1+1) = insert (n+2) (Icc 2 (n+1)) := by
      ext m
      simp only [mem_Icc, mem_insert]
      omega
    rw [hs, prod_insert (by simp), ih]
    push_cast
    field_simp
    ring

lemma one_div_le_V (w : ℕ) (hw : 1 ≤ w) : 1/(w:ℝ) ≤ V w := by
  have heq : (∏ m ∈ Icc 2 w, (1-1/(m:ℝ))) = 1/(w:ℝ) := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : w≠0)
    exact telescoping_complement n
  rw [← heq]
  apply product_antitone_subset (smallPrimes w) (Icc 2 w)
    (fun p => 1-1/(p:ℝ)) (filter_subset _ _)
  · intro m hm
    have hmR : (1:ℝ)≤(m:ℝ) := by exact_mod_cast (le_trans (by decide : 1 ≤ 2) (mem_Icc.mp hm).1)
    exact sub_nonneg.mpr ((div_le_one (by linarith)).mpr hmR)
  · intro m hm
    exact sub_le_self _ (by positivity)

lemma telescoping_double (n : ℕ) :
    (∏ m ∈ Icc 2 (n+1), (1+2/(m:ℝ))) =
      ((n+2:ℕ):ℝ)*((n+3:ℕ):ℝ)/6 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hs : Icc 2 (n+1+1) = insert (n+2) (Icc 2 (n+1)) := by
      ext m
      simp only [mem_Icc, mem_insert]
      omega
    rw [hs, prod_insert (by simp), ih]
    push_cast
    field_simp
    ring

lemma doubled_prime_product_le (c w : ℕ) (hw : 2 ≤ w) :
    (∏ p ∈ activePrimes c w, (1+2*(1/(p:ℝ)))) ≤ (w:ℝ)^2 := by
  have hsub : activePrimes c w ⊆ Icc 2 w := by
    intro p hp
    obtain ⟨hpp, hpw, _⟩ := mem_activePrimes.mp hp
    exact mem_Icc.mpr ⟨hpp.two_le, hpw⟩
  have hmono :
      (∏ p ∈ activePrimes c w, (1 + 2 / (p : ℝ))) ≤
        ∏ p ∈ Icc 2 w, (1 + 2 / (p : ℝ)) := by
    apply product_mono_subset (activePrimes c w) (Icc 2 w)
      (fun p : ℕ => 1 + 2 / (p : ℝ)) hsub
    intro p _hp
    have hp0 : (0 : ℝ) ≤ 2 / (p : ℝ) :=
      div_nonneg (by norm_num) (Nat.cast_nonneg p)
    linarith
  calc
    (∏ p ∈ activePrimes c w, (1+2*(1/(p:ℝ))))
        ≤ ∏ p ∈ Icc 2 w, (1+2/(p:ℝ)) := by
      simpa only [mul_one_div] using hmono
    _ = ((w:ℝ)+1)*((w:ℝ)+2)/6 := by
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : w ≠ 0)
      calc
        (∏ p ∈ Icc 2 (n + 1), (1 + 2 / (p : ℝ))) =
            ((n + 2 : ℕ) : ℝ) * ((n + 3 : ℕ) : ℝ) / 6 :=
          telescoping_double n
        _ = (((n + 1 : ℕ) : ℝ) + 1) * (((n + 1 : ℕ) : ℝ) + 2) / 6 := by
          push_cast <;> ring
    _ ≤ (w:ℝ)^2 := by
      have hwR : (2:ℝ)≤(w:ℝ) := by exact_mod_cast hw
      nlinarith

lemma not_dvd_linear_of_dvd_coefficient (c m p : ℕ) (hc : 1 ≤ c) (hm : 1 ≤ m)
    (hp : Nat.Prime p) (hpc : p∣c) : ¬p∣c*m-1 := by
  intro h
  have hprod : p∣c*m := dvd_mul_of_dvd_left hpc m
  have hcm : 1≤c*m := Nat.mul_le_mul hc hm
  have hid : c*m-(c*m-1)=1 := by omega
  have h1 : p∣1 := hid ▸ Nat.dvd_sub hprod h
  exact hp.not_dvd_one h1

lemma rough_iff_active (c m w : ℕ) (hc : 3 ≤ c) (hm : 1 ≤ m) :
    w < Nat.minFac (c*m-1) ↔ ∀ p ∈ activePrimes c w, ¬p∣c*m-1 := by
  have hcm : 3 ≤ c * m := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul hc hm
  have hnum : 1 < c * m - 1 := by omega
  constructor
  · intro h p hp hdiv
    have hpp : Nat.Prime p := (mem_activePrimes.mp hp).1
    have hpw : p ≤ w := (mem_activePrimes.mp hp).2.1
    have hmin : Nat.minFac (c * m - 1) ≤ p :=
      Nat.minFac_le_of_dvd hpp.two_le hdiv
    exact (not_lt_of_ge (hmin.trans hpw)) h
  · intro h
    by_contra hmin
    have hminw : Nat.minFac (c * m - 1) ≤ w := le_of_not_gt hmin
    have hpp : Nat.Prime (Nat.minFac (c * m - 1)) :=
      Nat.minFac_prime (by omega : c * m - 1 ≠ 1)
    have hdiv : Nat.minFac (c * m - 1) ∣ c * m - 1 :=
      Nat.minFac_dvd (c * m - 1)
    have hpc : ¬ (Nat.minFac (c * m - 1) ∣ c) := by
      intro hpc
      exact not_dvd_linear_of_dvd_coefficient c m (Nat.minFac (c * m - 1))
        (by omega) hm hpp hpc hdiv
    exact h (Nat.minFac (c * m - 1))
      (mem_activePrimes.mpr ⟨hpp, hminw, hpc⟩) hdiv

lemma sum_Ioc_eq_sum_fin (U H : ℕ) (f : ℕ → ℝ) :
    (∑ m ∈ Ioc U (U+H), f m) = ∑ i : Fin H, f (U+i.val+1) := by
  classical
  symm
  refine Finset.sum_bij
    (fun (i : Fin H) (_hi : i ∈ (univ : Finset (Fin H))) => U + i.val + 1)
    ?_ ?_ ?_ ?_
  · intro i _hi
    have hiH : i.val < H := i.isLt
    change U + i.val + 1 ∈ Ioc U (U + H)
    exact mem_Ioc.mpr ⟨by omega, by omega⟩
  · intro i _hi j _hj hij
    apply Fin.ext
    change U + i.val + 1 = U + j.val + 1 at hij
    exact Nat.add_left_cancel (Nat.add_right_cancel hij)
  · intro m hm
    obtain ⟨hmlo, hmhi⟩ := mem_Ioc.mp hm
    refine ⟨⟨m - (U + 1), by omega⟩, mem_univ _, ?_⟩
    change U + (m - (U + 1)) + 1 = m
    omega
  · intro i _hi
    rfl

lemma roughScales_card_eq (c U H w : ℕ) (hc : 3 ≤ c) :
    ((roughScales c U H w).card : ℝ) =
      ∑ i : Fin H, indicator (∀ p ∈ activePrimes c w, ¬p∣c*(U+i.val+1)-1) := by
  classical
  calc
    ((roughScales c U H w).card : ℝ) =
        ∑ m ∈ Ioc U (U + H), indicator (w < Nat.minFac (c * m - 1)) := by
      simp only [roughScales, indicator, Finset.sum_boole]
    _ = ∑ i : Fin H, indicator (w < Nat.minFac (c * (U + i.val + 1) - 1)) :=
      sum_Ioc_eq_sum_fin U H (fun m => indicator (w < Nat.minFac (c * m - 1)))
    _ = ∑ i : Fin H,
        indicator (∀ p ∈ activePrimes c w, ¬p ∣ c * (U + i.val + 1) - 1) := by
      apply Finset.sum_congr rfl
      intro i _hi
      simp only [indicator, rough_iff_active c (U + i.val + 1) w hc (by omega)]

/-- The error uses the full products of excluded primes, including products exceeding H. -/
theorem sieve_absolute_error (c U H w : ℕ) (hc : 3 ≤ c) (hw : 2 ≤ w) :
    |((roughScales c U H w).card : ℝ)-(H:ℝ)*Vcoeff c w| ≤
      (w:ℝ)^(sieveLevel w+1) +
      (H:ℝ)*(w:ℝ)^2/(2:ℝ)^(sieveLevel w+1) := by
  classical
  have hx0 : ∀ p ∈ activePrimes c w, (0 : ℝ) ≤ 1 / (p : ℝ) := by
    intro p _hp
    exact div_nonneg (by norm_num) (Nat.cast_nonneg p)
  have hx1 : ∀ p ∈ activePrimes c w, (1 : ℝ) / (p : ℝ) ≤ 1 := by
    intro p hp
    have hpR : (1 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (mem_activePrimes.mp hp).1.one_le
    exact (div_le_one (by linarith)).mpr hpR
  have hk : Even (sieveLevel w) := by
    refine ⟨4 * (Nat.log 2 w + 1), ?_⟩
    unfold sieveLevel
    omega
  have hcount : ∀ t ∈ (activePrimes c w).powerset,
      t.card ≤ sieveLevel w + 1 →
      |(∑ i : Fin H, indicator (∀ p ∈ t, p ∣ c * (U + i.val + 1) - 1)) -
        (H : ℝ) * (∏ p ∈ t, 1 / (p : ℝ))| ≤ 1 := by
    intro t ht _htk
    apply prime_intersection_error c U H (by omega) t
    intro p hp
    have hpa : p ∈ activePrimes c w := (mem_powerset.mp ht) hp
    exact ⟨(mem_activePrimes.mp hpa).1, (mem_activePrimes.mp hpa).2.2⟩
  have hsize : ∀ j ≤ sieveLevel w + 1,
      ((((activePrimes c w).powerset).filter (fun t => t.card ≤ j)).card : ℝ) ≤
        (w : ℝ) ^ (sieveLevel w + 1) := by
    intro j hj
    have hcard := truncated_prime_subsets_card (activePrimes c w) w j
      (by omega) (fun p hp =>
        ⟨(mem_activePrimes.mp hp).1, (mem_activePrimes.mp hp).2.1⟩)
    have hpow : w ^ j ≤ w ^ (sieveLevel w + 1) :=
      Nat.pow_le_pow_right (by omega : 1 ≤ w) hj
    exact_mod_cast (hcard.trans hpow)
  have hraw := @finite_bonferroni_count ℕ _ (Fin H) _
    (activePrimes c w)
    (fun (p : ℕ) (i : Fin H) => p ∣ c * (U + i.val + 1) - 1)
    (fun _ _ => Classical.propDecidable _)
    (fun p : ℕ => (1 : ℝ) / (p : ℝ))
    (H : ℝ) ((w : ℝ) ^ (sieveLevel w + 1)) (sieveLevel w)
    (Nat.cast_nonneg H) (pow_nonneg (Nat.cast_nonneg w) _)
    hx0 hx1 hk hcount hsize
  have hdec :
      (fun (p : ℕ) (i : Fin H) => Classical.propDecidable (p ∣ c * (U + i.val + 1) - 1)) =
      (fun (p : ℕ) (i : Fin H) => Nat.decidable_dvd p (c * (U + i.val + 1) - 1)) :=
    Subsingleton.elim _ _
  rw [hdec] at hraw
  have hraw' :
    |(∑ i : Fin H,
        indicator (∀ p ∈ activePrimes c w, ¬p ∣ c * (U + i.val + 1) - 1)) -
        (H : ℝ) * Vcoeff c w| ≤
      (w : ℝ) ^ (sieveLevel w + 1) +
        (H : ℝ) * ((∏ p ∈ activePrimes c w, (1 + 2 * (1 / (p : ℝ)))) /
          (2 : ℝ) ^ (sieveLevel w + 1)) := by
    simpa only [indicator, productComplement, Vcoeff] using hraw
  rw [← roughScales_card_eq c U H w hc] at hraw'
  have hquot :
      (∏ p ∈ activePrimes c w, (1 + 2 * (1 / (p : ℝ)))) /
          (2 : ℝ) ^ (sieveLevel w + 1) ≤
        (w : ℝ) ^ 2 / (2 : ℝ) ^ (sieveLevel w + 1) :=
    div_le_div_of_nonneg_right (doubled_prime_product_le c w hw)
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
  have hbudget := add_le_add_right
    (mul_le_mul_of_nonneg_left hquot (Nat.cast_nonneg H))
    ((w : ℝ) ^ (sieveLevel w + 1))
  exact hraw'.trans (by simpa only [mul_div_assoc] using hbudget)

lemma sieve_tail_small (w : ℕ) (hw : 2 ≤ w) :
    4*(w:ℝ)^3 ≤ (2:ℝ)^(sieveLevel w+1) := by
  let m : ℕ := Nat.log 2 w + 1
  have hm : 1 ≤ m := Nat.succ_le_succ (Nat.zero_le (Nat.log 2 w))
  have hw2 : w ≤ 2 ^ m :=
    (Nat.lt_pow_succ_log_self (b := 2) (by decide) w).le
  have hpow : 4 * w ^ 3 ≤ 2 ^ (8 * m + 1) := by
    calc
      4 * w ^ 3 ≤ 4 * (2 ^ m) ^ 3 :=
        Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hw2 3)
      _ = (2 ^ m) ^ 3 * 2 ^ 2 := by ring
      _ = 2 ^ (m * 3 + 2) := by rw [pow_add 2 (m * 3) 2, pow_mul 2 m 3]
      _ ≤ 2 ^ (8 * m + 1) :=
        Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega)
  change 4 * (w : ℝ) ^ 3 ≤ (2 : ℝ) ^ (8 * m + 1)
  exact_mod_cast hpow

/-- A genuinely uniform relative sieve. The length requirement is explicit. -/
theorem sieve_relative (c U H w : ℕ) (hc : 3 ≤ c) (hw : 2 ≤ w)
    (hH : sieveLength w ≤ H) :
    (H:ℝ)*Vcoeff c w/2 ≤ ((roughScales c U H w).card:ℝ) ∧
      ((roughScales c U H w).card:ℝ) ≤ 3*((H:ℝ)*Vcoeff c w)/2 := by
  have hwR : (0 : ℝ) < (w : ℝ) := by exact_mod_cast (by omega : 0 < w)
  have hkR : (0 : ℝ) < (2 : ℝ) ^ (sieveLevel w + 1) := by positivity
  have hfourw : (0 : ℝ) < 4 * (w : ℝ) := mul_pos (by norm_num) hwR
  have hE := sieve_absolute_error c U H w hc hw
  have ht := sieve_tail_small w hw
  have hlen : 4 * (w : ℝ) ^ (sieveLevel w + 2) ≤ (H : ℝ) := by
    change 4 * w ^ (sieveLevel w + 2) ≤ H at hH
    exact_mod_cast hH
  have h1 : (w : ℝ) ^ (sieveLevel w + 1) ≤ (H : ℝ) / (4 * (w : ℝ)) := by
    apply (le_div_iff₀ hfourw).mpr
    calc
      (w : ℝ) ^ (sieveLevel w + 1) * (4 * (w : ℝ)) =
          4 * (w : ℝ) ^ (sieveLevel w + 2) := by
        rw [pow_succ (w : ℝ) (sieveLevel w + 1)]
        ring
      _ ≤ (H : ℝ) := hlen
  have h2 : (H : ℝ) * (w : ℝ) ^ 2 / (2 : ℝ) ^ (sieveLevel w + 1) ≤
      (H : ℝ) / (4 * (w : ℝ)) := by
    apply (div_le_div_iff₀ hkR hfourw).mpr
    calc
      (H : ℝ) * (w : ℝ) ^ 2 * (4 * (w : ℝ)) =
          (H : ℝ) * (4 * (w : ℝ) ^ 3) := by ring
      _ ≤ (H : ℝ) * (2 : ℝ) ^ (sieveLevel w + 1) :=
        mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg H)
  have hV : 1 / (w : ℝ) ≤ Vcoeff c w :=
    (one_div_le_V w (by omega)).trans (V_le_Vcoeff c w)
  have hbudget : (w : ℝ) ^ (sieveLevel w + 1) +
      (H : ℝ) * (w : ℝ) ^ 2 / (2 : ℝ) ^ (sieveLevel w + 1) ≤
        (H : ℝ) * Vcoeff c w / 2 := by
    calc
      (w : ℝ) ^ (sieveLevel w + 1) +
          (H : ℝ) * (w : ℝ) ^ 2 / (2 : ℝ) ^ (sieveLevel w + 1) ≤
          (H : ℝ) / (4 * (w : ℝ)) + (H : ℝ) / (4 * (w : ℝ)) :=
        add_le_add h1 h2
      _ = (H : ℝ) * (1 / (w : ℝ)) / 2 := by
        field_simp [hwR.ne'] <;> ring
      _ ≤ (H : ℝ) * Vcoeff c w / 2 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hV (Nat.cast_nonneg H)) (by norm_num)
  have habs := abs_le.mp (hE.trans hbudget)
  constructor <;> linarith

end
end PrimeAbundance.Analytic
