/- An elementary lower bound for the number of primes.
Only finite binomial-coefficient factorization is used; no PNT hypothesis. -/
import PrimeAbundance.Target
import PrimeAbundance.AnalyticBounds
import Mathlib.Data.Nat.Choose.Factorization

set_option autoImplicit false
open scoped Classical
open scoped BigOperators
open Finset

namespace PrimeAbundance.Analytic
noncomputable section

lemma primesUpTo_mono {m n : ℕ} (hmn : m ≤ n) : primesUpTo m ⊆ primesUpTo n := by
  intro p hp
  obtain ⟨hpi,hprime⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp hpi).1,(mem_Icc.mp hpi).2.trans hmn⟩,hprime⟩

lemma centralBinom_prime_power_le (m p : ℕ) (hm : 0 < m) :
    p^(Nat.centralBinom m).factorization p ≤ 2*m := by
  exact Nat.pow_factorization_choose_le (n := 2*m) (k := m) (p := p) (by positivity)

lemma centralBinom_primeFactors_subset (m : ℕ) (hm : 0 < m) :
    (Nat.centralBinom m).primeFactors ⊆ primesUpTo (2*m) := by
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hdiv := Nat.dvd_of_mem_primeFactors hp
  have he : 0 < (Nat.centralBinom m).factorization p :=
    hprime.factorization_pos_of_dvd (Nat.centralBinom_ne_zero m) hdiv
  have hple : p ≤ p^(Nat.centralBinom m).factorization p := by
    simpa only [pow_one] using Nat.pow_le_pow_right hprime.one_le he
  exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hprime.two_le,
    hple.trans (centralBinom_prime_power_le m p hm)⟩,hprime⟩

lemma centralBinom_le_primeCount_power (m : ℕ) (hm : 0 < m) :
    Nat.centralBinom m ≤ (2*m)^(primesUpTo (2*m)).card := by
  have hnonzero := Nat.centralBinom_ne_zero m
  calc
    Nat.centralBinom m=(Nat.centralBinom m).factorization.prod (fun p e => p^e) :=
      (Nat.factorization_prod_pow_eq_self hnonzero).symm
    _ ≤ ∏ _p∈(Nat.centralBinom m).primeFactors,2*m := by
      change (∏ p∈(Nat.centralBinom m).primeFactors,p^(Nat.centralBinom m).factorization p)≤_
      apply prod_le_prod (fun _ _ => Nat.zero_le _)
      intro p hp
      exact centralBinom_prime_power_le m p hm
    _ = (2*m)^(Nat.centralBinom m).primeFactors.card := by simp
    _ ≤ (2*m)^(primesUpTo (2*m)).card := Nat.pow_le_pow_right (by positivity)
      (card_le_card (centralBinom_primeFactors_subset m hm))

lemma centralBinom_count_log (m : ℕ) (hm : 0 < m) :
    (m:ℝ)*Real.log 4 ≤ (((primesUpTo (2*m)).card:ℝ)+1)*Real.log ((2*m:ℕ):ℝ) := by
  have hlow := Nat.four_pow_le_two_mul_self_mul_centralBinom m hm
  have hhigh := centralBinom_le_primeCount_power m hm
  have hnat : 4^m ≤ (2*m)^((primesUpTo (2*m)).card+1) := by
    calc
      _ ≤ 2*m*Nat.centralBinom m := hlow
      _ ≤ 2*m*(2*m)^(primesUpTo (2*m)).card := Nat.mul_le_mul_left (2*m) hhigh
      _ = _ := by rw [pow_succ]; ring
  have hnatR : ((4^m:ℕ):ℝ) ≤ (((2*m)^((primesUpTo (2*m)).card+1):ℕ):ℝ) := by
    exact_mod_cast hnat
  have hlog := Real.log_le_log (by positivity : (0:ℝ) < ((4^m:ℕ):ℝ)) hnatR
  simpa only [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow,Nat.cast_add,Nat.cast_one] using hlog

lemma log_two_mul_nat_le_half (m : ℕ) (hm : 8 ≤ m) :
    Real.log ((2*m:ℕ):ℝ) ≤ (m:ℝ)/2 := by
  have hmR : (8:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hpos : (0:ℝ) < (m:ℝ)/4 := by positivity
  have heq : Real.log ((2*m:ℕ):ℝ)=Real.log 8+Real.log ((m:ℝ)/4) := by
    rw [←Real.log_mul (by norm_num) hpos.ne']
    congr 1
    push_cast
    ring
  have h8 : Real.log 8 ≤ 3 := by
    rw [show (8:ℝ)=2^3 by norm_num,Real.log_pow]
    norm_num
    linarith [log_two_lt_one]
  rw [heq]
  have h := Real.log_le_sub_one_of_pos hpos
  linarith

lemma primeCount_even_lower (m : ℕ) (hm : 8 ≤ m) :
    (m:ℝ)/(2*Real.log ((2*m:ℕ):ℝ)) ≤ ((primesUpTo (2*m)).card:ℝ) := by
  have hm0 : 0 < m := by omega
  have h := centralBinom_count_log m hm0
  have hl := log_two_mul_nat_le_half m hm
  have h4 : 1 ≤ Real.log 4 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
    norm_num
    linarith [half_le_log_two]
  have hlog : 0 < Real.log ((2*m:ℕ):ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < 2*m))
  apply (div_le_iff₀ (by positivity)).mpr
  have hm4 := mul_le_mul_of_nonneg_left h4 (by positivity : (0:ℝ)≤(m:ℝ))
  nlinarith

/-- This explicit Chebyshev lower bound is sufficient for relative prime density. -/
theorem primeCount_lower (N : ℕ) (hN : 16 ≤ N) :
    (N:ℝ)/(6*Real.log (N:ℝ)) ≤ ((primesUpTo N).card:ℝ) := by
  let m := N/2
  have hm : 8 ≤ m := (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr (by omega)
  have h2m : 2*m ≤ N := by simpa [m,mul_comm] using Nat.div_mul_le_self N 2
  have h3m : N ≤ 3*m := by
    have h := Nat.mod_add_div N 2
    have hr := Nat.mod_lt N (by decide : 0 < 2)
    dsimp [m] at *
    omega
  have hmR : (0:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hlogm : 0 < Real.log ((2*m:ℕ):ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < 2*m))
  have hlogN : 0 < Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have h2mR : ((2*m:ℕ):ℝ) ≤ (N:ℝ) := by exact_mod_cast h2m
  have hlog := Real.log_le_log (by positivity : (0:ℝ) < ((2*m:ℕ):ℝ)) h2mR
  have hcard : ((primesUpTo (2*m)).card:ℝ) ≤ ((primesUpTo N).card:ℝ) := by
    exact_mod_cast card_le_card (primesUpTo_mono h2m)
  calc
    _ ≤ (3*(m:ℝ))/(6*Real.log (N:ℝ)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast h3m
    _ = (m:ℝ)/(2*Real.log (N:ℝ)) := by ring
    _ ≤ (m:ℝ)/(2*Real.log ((2*m:ℕ):ℝ)) :=
      div_le_div_of_nonneg_left hmR.le (by positivity) (by linarith)
    _ ≤ ((primesUpTo (2*m)).card:ℝ) := primeCount_even_lower m hm
    _ ≤ ((primesUpTo N).card:ℝ) := hcard

lemma primeCount_pos (N : ℕ) (hN : 16 ≤ N) : (0:ℝ) < ((primesUpTo N).card:ℝ) := by
  have hlog : 0 < Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  exact (div_pos (by positivity) (by positivity)).trans_le (primeCount_lower N hN)

end
end PrimeAbundance.Analytic
