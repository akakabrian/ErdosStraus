/-
The third divisor moment, proved from Dirichlet convolution and finite divisor sums.
The analytic proof needs only a logarithmic upper bound, not an asymptotic formula.
Uncompiled proof-source candidate, Lean/mathlib 4.27.0.
-/
import PrimeAbundance.Sums
import Mathlib.NumberTheory.ArithmeticFunction.Zeta

set_option autoImplicit false
open scoped Classical
open scoped BigOperators
open Finset
open ArithmeticFunction

namespace PrimeAbundance.Analytic
noncomputable section

def tau (n : ℕ) : ℕ := n.divisors.card

def dk (k : ℕ) : ArithmeticFunction ℕ := ArithmeticFunction.zeta^k

/-- Exact change of variables (n,d) ↔ (d,n/d); no endpoint is dropped. -/
lemma divisor_fubini (N : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ n∈Icc 1 N, ∑ d∈n.divisors, F d (n/d)) =
      ∑ d∈Icc 1 N, ∑ m∈Icc 1 (N/d), F d m := by
  classical
  rw [sum_sigma', sum_sigma']
  refine sum_bij (fun p _ => ⟨p.2,p.1/p.2⟩) ?_ ?_ ?_ ?_
  · rintro ⟨n,d⟩ hp
    obtain ⟨hn,hd⟩ := mem_sigma.mp hp
    obtain ⟨hn1,hnN⟩ := mem_Icc.mp hn
    have hdn := (Nat.mem_divisors.mp hd).1
    have hdpos : 0<d := Nat.pos_of_dvd_of_pos hdn hn1
    have hdle : d≤n := Nat.le_of_dvd hn1 hdn
    refine mem_sigma.mpr ⟨mem_Icc.mpr ⟨hdpos,hdle.trans hnN⟩,
      mem_Icc.mpr ⟨Nat.div_pos hdle hdpos, Nat.div_le_div_right hnN⟩⟩
  · rintro ⟨n,d⟩ hp ⟨n',d'⟩ hp' h
    have hd : d=d' := congrArg Sigma.fst h
    subst d'
    have hq : n/d=n'/d := by simpa using congrArg Sigma.snd h
    have hnd := Nat.div_mul_cancel (Nat.mem_divisors.mp (mem_sigma.mp hp).2).1
    have hn'd := Nat.div_mul_cancel (Nat.mem_divisors.mp (mem_sigma.mp hp').2).1
    rw [hq] at hnd
    have hn : n=n' := hnd.symm.trans hn'd
    subst n'
    rfl
  · rintro ⟨d,m⟩ hp
    obtain ⟨hd,hm⟩ := mem_sigma.mp hp
    obtain ⟨hd1,hdN⟩ := mem_Icc.mp hd
    obtain ⟨hm1,hmN⟩ := mem_Icc.mp hm
    have hdm : d*m≤N := by
      have h := (Nat.le_div_iff_mul_le hd1).mp hmN
      nlinarith
    refine ⟨⟨d*m,d⟩, ?_, ?_⟩
    · exact mem_sigma.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hd1 hm1,hdm⟩,
        Nat.mem_divisors.mpr ⟨dvd_mul_right d m, by positivity⟩⟩
    · simp [Nat.mul_div_cancel_left m hd1]
  · rintro ⟨n,d⟩ hp
    rfl

lemma dk_succ (k n : ℕ) : dk (k+1) n = ∑ d∈n.divisors, dk k d := by
  rw [dk, pow_succ, ArithmeticFunction.mul_zeta_apply]
  rfl

lemma dk_one {n : ℕ} (hn : n≠0) : dk 1 n=1 := by
  simp [dk, ArithmeticFunction.zeta_apply_ne hn]

lemma dk_two (n : ℕ) : dk 2 n=tau n := by
  rw [show 2=1+1 by decide, dk_succ]
  have h : ∀ d∈n.divisors, dk 1 d=1 := fun d hd =>
    dk_one (Nat.ne_zero_of_lt (Nat.pos_of_mem_divisors hd))
  simp_rw [sum_congr rfl h]
  simp [tau]

lemma dk_multiplicative (k : ℕ) : (dk k).IsMultiplicative := by
  induction k with
  | zero => simpa [dk] using (ArithmeticFunction.isMultiplicative_one (R := ℕ))
  | succ k ih =>
    simpa [dk, pow_succ] using ih.mul ArithmeticFunction.isMultiplicative_zeta

lemma hockey_stick (k e : ℕ) :
    (∑ j∈range (e+1), (j+k).choose k) = (e+k+1).choose (k+1) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [sum_range_succ, ih]
    have h := Nat.choose_succ_succ (e+k+1) k
    simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h.symm

lemma dk_prime_pow (k p e : ℕ) (hp : Nat.Prime p) :
    dk (k+1) (p^e) = (e+k).choose k := by
  induction k generalizing e with
  | zero => simp [dk, hp.ne_zero]
  | succ k ih =>
    rw [dk_succ, Nat.divisors_prime_pow hp, sum_map]
    simp only [Function.Embedding.coeFn_mk]
    simp_rw [ih]
    simpa only [Nat.add_assoc] using hockey_stick k e

/-- A direct polynomial proof of the only local comparison required. -/
lemma cube_le_choose_seven (e : ℕ) : (e+1)^3 ≤ (e+7).choose 7 := by
  cases e with
  | zero => norm_num
  | succ t =>
    have hc := Nat.ascFactorial_eq_factorial_mul_choose (t+1) 7
    norm_num [Nat.ascFactorial] at hc
    have hid : (t+2)*(t+3)*(t+4)*(t+5)*(t+6)*(t+7)*(t+8) =
        5040*(t+2)^3 +
          (t^7+35*t^6+511*t^5+4025*t^4+13384*t^3+18620*t^2+8784*t) := by ring
    have hle : 5040*(t+2)^3 ≤
        (t+2)*(t+3)*(t+4)*(t+5)*(t+6)*(t+7)*(t+8) := by
      rw [hid]
      omega
    have hc' : (t+2)*(t+3)*(t+4)*(t+5)*(t+6)*(t+7)*(t+8) =
        5040*((t+1+7).choose 7) := by nlinarith [hc]
    rw [hc'] at hle
    nlinarith

/-- Pointwise multiplication of divisor counts is not confused with convolution. -/
theorem tau_cube_le_d8 (n : ℕ) : tau n^3 ≤ dk 8 n := by
  by_cases hn : n=0
  · simp [hn,tau,dk]
  let f : ArithmeticFunction ℕ := (dk 2).ppow 3
  have hf : f.IsMultiplicative := (dk_multiplicative 2).ppow
  have hg := dk_multiplicative 8
  have hfeq : f n=tau n^3 := by
    dsimp [f]
    rw [ArithmeticFunction.ppow_apply (by decide : 0<3), dk_two]
  rw [← hfeq, hf.multiplicative_factorization f hn,
    hg.multiplicative_factorization (dk 8) hn]
  change (∏ p∈n.primeFactors, f (p^n.factorization p)) ≤
    ∏ p∈n.primeFactors, dk 8 (p^n.factorization p)
  apply prod_le_prod (fun _ _ => Nat.zero_le _)
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  dsimp [f]
  rw [ArithmeticFunction.ppow_apply (by decide : 0<3)]
  rw [show 2=1+1 by decide, dk_prime_pow 1 p _ hpp,
    show 8=7+1 by decide, dk_prime_pow 7 p _ hpp]
  simpa using cube_le_choose_seven (n.factorization p)

/-- Harmonic Dirichlet-convolution sum, with no assertion about divisor distribution. -/
lemma dk_harmonic_bound (k N : ℕ) :
    (∑ n∈Icc 1 N, (dk (k+1) n:ℝ)/(n:ℝ)) ≤ (H N)^(k+1) := by
  induction k with
  | zero =>
    have h : (∑ n∈Icc 1 N, (dk 1 n:ℝ)/(n:ℝ))=H N := by
      apply sum_congr rfl
      intro n hn
      rw [dk_one (by have := (mem_Icc.mp hn).1; omega), Nat.cast_one]
    simpa using h.le
  | succ k ih =>
    have hid : (∑ n∈Icc 1 N, (dk (k+1+1) n:ℝ)/(n:ℝ)) =
        ∑ d∈Icc 1 N, ∑ m∈Icc 1 (N/d),
          (dk (k+1) d:ℝ)/((d:ℝ)*(m:ℝ)) := by
      rw [← divisor_fubini]
      apply sum_congr rfl
      intro n hn
      rw [dk_succ, Nat.cast_sum, sum_div]
      apply sum_congr rfl
      intro d hd
      have hdn := Nat.div_mul_cancel (Nat.mem_divisors.mp hd).1
      have hR : (d:ℝ)*((n/d:ℕ):ℝ)=(n:ℝ) := by
        exact_mod_cast (by nlinarith : d*(n/d)=n)
      rw [hR]
    rw [hid]
    calc
      (∑ d∈Icc 1 N, ∑ m∈Icc 1 (N/d), (dk (k+1) d:ℝ)/((d:ℝ)*(m:ℝ)))
          = ∑ d∈Icc 1 N, ((dk (k+1) d:ℝ)/(d:ℝ))*H (N/d) := by
        apply sum_congr rfl
        intro d hd
        rw [H, mul_sum]
        apply sum_congr rfl
        intro m hm
        ring
      _ ≤ ∑ d∈Icc 1 N, ((dk (k+1) d:ℝ)/(d:ℝ))*H N := by
        apply sum_le_sum
        intro d hd
        exact mul_le_mul_of_nonneg_left (H_mono (Nat.div_le_self N d)) (by positivity)
      _ = (∑ d∈Icc 1 N, (dk (k+1) d:ℝ)/(d:ℝ))*H N := by rw [sum_mul]
      _ ≤ (H N)^(k+1)*H N := mul_le_mul_of_nonneg_right ih (H_nonneg N)
      _ = (H N)^(k+1+1) := (pow_succ (H N) (k+1)).symm

lemma dk_prefix_bound (k N : ℕ) :
    (∑ n∈Icc 1 N, (dk (k+2) n:ℝ)) ≤ (N:ℝ)*(H N)^(k+1) := by
  have hid : (∑ n∈Icc 1 N, (dk (k+2) n:ℝ)) =
      ∑ d∈Icc 1 N, ((N/d:ℕ):ℝ)*(dk (k+1) d:ℝ) := by
    have hrewrite : (∑ n∈Icc 1 N, (dk (k+2) n:ℝ)) =
        ∑ n∈Icc 1 N, ∑ d∈n.divisors, (dk (k+1) d:ℝ) := by
      apply sum_congr rfl
      intro n hn
      rw [show k+2=(k+1)+1 by omega, dk_succ, Nat.cast_sum]
    rw [hrewrite, divisor_fubini N (fun d _ => (dk (k+1) d:ℝ))]
    simp
  rw [hid]
  calc
    (∑ d∈Icc 1 N, ((N/d:ℕ):ℝ)*(dk (k+1) d:ℝ)) ≤
        ∑ d∈Icc 1 N, (N:ℝ)*((dk (k+1) d:ℝ)/(d:ℝ)) := by
      apply sum_le_sum
      intro d hd
      have hdR : (0:ℝ)<(d:ℝ) := by exact_mod_cast (mem_Icc.mp hd).1
      have hdiv : ((N/d:ℕ):ℝ)≤(N:ℝ)/(d:ℝ) := by
        apply (le_div_iff₀ hdR).mpr
        exact_mod_cast Nat.div_mul_le_self N d
      have h := mul_le_mul_of_nonneg_right hdiv
        (by positivity : (0:ℝ)≤(dk (k+1) d:ℝ))
      convert h using 1 <;> ring
    _ = (N:ℝ)*(∑ d∈Icc 1 N, (dk (k+1) d:ℝ)/(d:ℝ)) := by rw [mul_sum]
    _ ≤ (N:ℝ)*(H N)^(k+1) :=
      mul_le_mul_of_nonneg_left (dk_harmonic_bound k N) (by positivity)

/-- The elementary third divisor moment used for determinant differences. -/
theorem tau_cube_prefix (N : ℕ) :
    (∑ n∈Icc 1 N, (tau n:ℝ)^3) ≤ (N:ℝ)*(1+Real.log (N:ℝ))^7 := by
  by_cases hN : N=0
  · simp [hN]
  have hN1 : 1≤N := Nat.one_le_iff_ne_zero.mpr hN
  calc
    (∑ n∈Icc 1 N, (tau n:ℝ)^3) ≤ ∑ n∈Icc 1 N, (dk 8 n:ℝ) := by
      apply sum_le_sum
      intro n hn
      exact_mod_cast tau_cube_le_d8 n
    _ ≤ (N:ℝ)*(H N)^7 := by simpa using dk_prefix_bound 6 N
    _ ≤ (N:ℝ)*(1+Real.log (N:ℝ))^7 := by
      gcongr
      · exact H_nonneg N
      · exact H_le N

end
end PrimeAbundance.Analytic
