/-
A weak Mertens lower bound proved with finite geometric products and finite Markov.
Only Chebyshev's proved upper bound from mathlib is imported. No PNT, unproved
external Mertens theorem, infinite Euler product, or sieve hypothesis is used.
Uncompiled proof-source candidate, Lean/mathlib 4.27.0.
-/
import PrimeAbundance.Sieve
import PrimeAbundance.TensorSums
import Mathlib.NumberTheory.Chebyshev

set_option autoImplicit false
open scoped Classical
open scoped BigOperators
open Finset

namespace PrimeAbundance.Analytic
noncomputable section

lemma log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
lemma log_two_lt_one : Real.log 2 < 1 := by
  have h := Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ)<2) (by norm_num : (2:ℝ)≠1)
  norm_num at h ⊢
  exact h

lemma prime_log_weight_nonneg (p : ℕ) : 0 ≤ Real.log (p:ℝ)/((p:ℝ)-1) := by
  by_cases hp : p=0
  · simp [hp]
  · have hp1 : (1:ℝ)≤(p:ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hp)
    exact div_nonneg (Real.log_nonneg hp1) (sub_nonneg.mpr hp1)

/-- Elementary dyadic partial summation of the Chebyshev upper bound. -/
lemma weighted_prime_log_le (w : ℕ) :
    (∑ p ∈ smallPrimes w, Real.log (p:ℝ)/((p:ℝ)-1)) ≤
      4*((Nat.log 2 w+1:ℕ):ℝ)*Real.log 2 := by
  let k := Nat.log 2 w
  let block : ℕ → Finset ℕ := fun j => (Ioc (2^j) (2^(j+1))).filter Nat.Prime
  have hcover : ∀ p ∈ smallPrimes w, ∃ j ∈ range (k+1), p ∈ block j := by
    intro p hp
    obtain ⟨hpp, hpw⟩ := mem_smallPrimes.mp hp
    let j := Nat.log 2 (p-1)
    have hp0 : p-1≠0 := by have := hpp.two_le; omega
    have hlo := Nat.pow_log_le_self 2 hp0
    have hhi := Nat.lt_pow_succ_log_self (b := 2) (by decide) (p-1)
    have hjk : j≤k := Nat.log_monotone ((Nat.sub_le p 1).trans hpw)
    refine ⟨j, mem_range.mpr (by omega), ?_⟩
    apply mem_filter.mpr
    refine ⟨mem_Ioc.mpr ?_, hpp⟩
    dsimp [j] at *
    have := hpp.two_le
    constructor <;> omega
  have hblock : ∀ j, (∑ p ∈ block j, Real.log (p:ℝ)/((p:ℝ)-1)) ≤ 4*Real.log 2 := by
    intro j
    have h2 : (0:ℝ)<(2:ℝ)^j := by positivity
    have htheta : (∑ p ∈ block j, Real.log (p:ℝ)) ≤
        Chebyshev.theta ((2^(j+1):ℕ):ℝ) := by
      unfold Chebyshev.theta
      rw [Nat.floor_natCast]
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        obtain ⟨hpI, hpp⟩ := mem_filter.mp hp
        obtain ⟨hp0, hpN⟩ := mem_Ioc.mp hpI
        exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨lt_trans (by positivity) hp0,hpN⟩,hpp⟩
      · intro p hp hnot
        exact Real.log_nonneg (by exact_mod_cast (mem_filter.mp hp).2.one_le)
    have htheta' := Chebyshev.theta_le_log4_mul_x
      (by positivity : (0:ℝ)≤((2^(j+1):ℕ):ℝ))
    calc
      (∑ p ∈ block j, Real.log (p:ℝ)/((p:ℝ)-1))
          ≤ ∑ p ∈ block j, Real.log (p:ℝ)/(2:ℝ)^j := by
        apply sum_le_sum
        intro p hp
        obtain ⟨hpI,hpp⟩ := mem_filter.mp hp
        have hden : (2:ℝ)^j ≤ (p:ℝ)-1 := by
          have hpj := (mem_Ioc.mp hpI).1
          have : 2^j+1≤p := hpj
          have hR : ((2^j:ℕ):ℝ)+1≤(p:ℝ) := by exact_mod_cast this
          push_cast at hR
          linarith
        exact div_le_div_of_nonneg_left
          (Real.log_nonneg (by exact_mod_cast hpp.one_le)) h2 hden
      _ = (∑ p ∈ block j, Real.log (p:ℝ))/(2:ℝ)^j := by rw [sum_div]
      _ ≤ (Real.log 4*((2^(j+1):ℕ):ℝ))/(2:ℝ)^j :=
        div_le_div_of_nonneg_right (htheta.trans htheta') h2.le
      _ = 4*Real.log 2 := by
        have hlog : Real.log (4:ℝ)=2*Real.log 2 := by
          rw [show (4:ℝ)=(2:ℝ)^2 by norm_num, Real.log_pow]
          norm_num
        rw [hlog, Nat.cast_pow, Nat.cast_ofNat, pow_succ]
        field_simp
        ring
  calc
    (∑ p ∈ smallPrimes w, Real.log (p:ℝ)/((p:ℝ)-1))
        ≤ ∑ j ∈ range (k+1), ∑ p ∈ block j, Real.log (p:ℝ)/((p:ℝ)-1) :=
      sum_le_sum_of_cover _ _ _ _ prime_log_weight_nonneg hcover
    _ ≤ ∑ _j ∈ range (k+1), 4*Real.log 2 := sum_le_sum (fun j _ => hblock j)
    _ = 4*((Nat.log 2 w+1:ℕ):ℝ)*Real.log 2 := by simp [k]; ring

abbrev PrimeExponentTuple (s : Finset ℕ) (J : ℕ) := s → Fin (J+1)

def primeTupleNumber (s : Finset ℕ) (J : ℕ) (e : PrimeExponentTuple s J) : ℕ :=
  ∏ p : s, (p:ℕ)^(e p).val

def primeTupleWeight (s : Finset ℕ) (J : ℕ) (e : PrimeExponentTuple s J) : ℝ :=
  1/(primeTupleNumber s J e:ℝ)

def primeTupleMass (s : Finset ℕ) (J : ℕ) : ℝ :=
  ∑ e : PrimeExponentTuple s J, primeTupleWeight s J e

lemma primeTupleNumber_pos (s : Finset ℕ) (J : ℕ)
    (hs : ∀ p∈s, Nat.Prime p) (e : PrimeExponentTuple s J) :
    0<primeTupleNumber s J e :=
  prod_pos (fun p _ => Nat.pow_pos (hs p p.property).pos)

lemma primeTupleNumber_factorization (s : Finset ℕ) (J : ℕ)
    (hs : ∀ p∈s, Nat.Prime p) (e : PrimeExponentTuple s J) (p : s) :
    (primeTupleNumber s J e).factorization p = (e p).val := by
  unfold primeTupleNumber
  rw [Nat.factorization_prod_apply
    (fun (q : s) _ => pow_ne_zero _ (hs q q.property).ne_zero)]
  have hterm : ∀ q : s,
      ((q:ℕ)^(e q).val).factorization p = if q=p then (e p).val else 0 := by
    intro q
    by_cases hq : q=p
    · subst q
      simp [Nat.factorization_pow, (hs p p.property).factorization]
    · have hqp : (q:ℕ)≠(p:ℕ) := fun h => hq (Subtype.ext h)
      simp [Nat.factorization_pow, (hs q q.property).factorization,
        Finsupp.single_apply, hq, hqp]
  simp_rw [hterm]
  simp

lemma primeTupleNumber_injective (s : Finset ℕ) (J : ℕ)
    (hs : ∀ p∈s, Nat.Prime p) : Function.Injective (primeTupleNumber s J) := by
  intro e f hef
  funext p
  apply Fin.ext
  have h := congrArg (fun n : ℕ => n.factorization p) hef
  simpa only [primeTupleNumber_factorization s J hs] using h

lemma primeTupleWeight_product (s : Finset ℕ) (J : ℕ) (e : PrimeExponentTuple s J) :
    primeTupleWeight s J e = ∏ p : s, (1/((p:ℕ):ℝ))^(e p).val := by
  simp only [primeTupleWeight, primeTupleNumber, Nat.cast_prod, Nat.cast_pow,
    one_div, prod_inv_distrib, inv_pow]

lemma primeTupleNumber_log (s : Finset ℕ) (J : ℕ)
    (hs : ∀ p∈s, Nat.Prime p) (e : PrimeExponentTuple s J) :
    Real.log (primeTupleNumber s J e:ℝ) =
      ∑ p : s, ((e p).val:ℝ)*Real.log ((p:ℕ):ℝ) := by
  unfold primeTupleNumber
  rw [Nat.cast_prod, Real.log_prod]
  · simp only [Nat.cast_pow, Real.log_pow]
  · intro p hp
    exact_mod_cast pow_ne_zero (e p).val (hs p p.property).ne_zero

lemma primeTupleMass_product (s : Finset ℕ) (J : ℕ) :
    primeTupleMass s J =
      ∏ p : s, ∑ j : Fin (J+1), (1/((p:ℕ):ℝ))^j.val := by
  unfold primeTupleMass
  simp_rw [primeTupleWeight_product]
  have hd : (fun (a b : s) => Subtype.instDecidableEq a b) =
      (fun a b => Classical.propDecidable (a = b)) := Subsingleton.elim _ _
  simpa only [hd] using
    sum_pi_product (fun (p : s) (j : Fin (J + 1)) => (1 / ((p : ℕ) : ℝ)) ^ j.val)

lemma primeTuple_log_moment (s : Finset ℕ) (J : ℕ)
    (hs : ∀ p∈s, Nat.Prime p) :
    (∑ e : PrimeExponentTuple s J,
        primeTupleWeight s J e * Real.log (primeTupleNumber s J e:ℝ)) ≤
      primeTupleMass s J * ∑ p∈s, Real.log (p:ℝ)/((p:ℝ)-1) := by
  classical
  simp_rw [primeTupleWeight_product, primeTupleNumber_log s J hs]
  have hprimeSum : (∑ p∈s, Real.log (p:ℝ)/((p:ℝ)-1)) =
      ∑ p : s, Real.log ((p:ℕ):ℝ)/(((p:ℕ):ℝ)-1) := by
    exact (Finset.sum_coe_sort s (fun p : ℕ => Real.log (p : ℝ) / ((p : ℝ) - 1))).symm
  rw [primeTupleMass_product, hprimeSum]
  apply product_weight_moment
    (fun (p : s) (j : Fin (J + 1)) => (1 / ((p : ℕ) : ℝ)) ^ j.val)
    (fun (p : s) (j : Fin (J + 1)) => (j.val : ℝ) * Real.log ((p : ℕ) : ℝ))
    (fun p : s => Real.log ((p : ℕ) : ℝ) / (((p : ℕ) : ℝ) - 1))
  · intro p j
    positivity
  · intro p
    let r : ℝ := 1/((p:ℕ):ℝ)
    have hpR : (1:ℝ)<((p:ℕ):ℝ) := by exact_mod_cast (hs p p.property).one_lt
    have hr0 : 0≤r := by dsimp [r]; positivity
    have hr1 : r<1 := by exact (div_lt_one (by linarith)).mpr hpR
    have hm := finite_geometric_moment_le r hr0 hr1 J
    have hlog : 0≤Real.log ((p:ℕ):ℝ) := Real.log_nonneg hpR.le
    have hp0 : (((p:ℕ):ℝ)) ≠ 0 := by linarith
    have hpm1 : (((p:ℕ):ℝ)-1) ≠ 0 := by linarith
    have hrid : r/(1-r)=1/(((p:ℕ):ℝ)-1) := by
      dsimp [r]
      field_simp [hp0, hpm1] <;> ring
    change (∑ j : Fin (J+1), r^j.val *
      ((j.val:ℝ)*Real.log ((p:ℕ):ℝ))) ≤
        (Real.log ((p:ℕ):ℝ)/(((p:ℕ):ℝ)-1)) *
          (∑ j : Fin (J+1), r^j.val)
    calc
      (∑ j : Fin (J+1), r^j.val*((j.val:ℝ)*Real.log ((p:ℕ):ℝ))) =
          (∑ j : Fin (J+1), r^j.val*(j.val:ℝ))*Real.log ((p:ℕ):ℝ) := by
        simp only [Finset.sum_mul, mul_assoc]
      _ ≤ ((r/(1-r))*(∑ j : Fin (J+1), r^j.val))*Real.log ((p:ℕ):ℝ) :=
        mul_le_mul_of_nonneg_right hm hlog
      _ = (Real.log ((p:ℕ):ℝ)/(((p:ℕ):ℝ)-1))*
          (∑ j : Fin (J+1), r^j.val) := by
        rw [hrid]
        ring

lemma primeTupleMass_times_V (w J : ℕ) :
    primeTupleMass (smallPrimes w) J * V w =
      ∏ p ∈ smallPrimes w, (1-(1/(p:ℝ))^(J+1)) := by
  classical
  -- Reindex precisely the two prime products. An unrestricted reverse
  -- `prod_coe_sort` can instead reindex the earlier exponent-tuple product.
  have hV : V w = ∏ p : smallPrimes w, (1-1/((p:ℕ):ℝ)) := by
    unfold V
    exact (Finset.prod_coe_sort (smallPrimes w) (fun p : ℕ => 1 - 1 / (p : ℝ))).symm
  have hresult : (∏ p ∈ smallPrimes w, (1-(1/(p:ℝ))^(J+1))) =
      ∏ p : smallPrimes w, (1-(1/((p:ℕ):ℝ))^(J+1)) := by
    exact (Finset.prod_coe_sort (smallPrimes w) (fun p : ℕ => 1 - (1 / (p : ℝ)) ^ (J + 1))).symm
  rw [primeTupleMass_product, hV, hresult, ← prod_mul_distrib]
  apply prod_congr rfl
  intro p hp
  rw [Fin.sum_univ_eq_sum_range]
  simpa only [mul_comm] using
    finite_geometric_identity (1/((p:ℕ):ℝ)) J

lemma primeTupleMass_not_too_small (w : ℕ) (hw : 2≤w) :
    (1:ℝ)/2 ≤ primeTupleMass (smallPrimes w) w * V w := by
  rw [primeTupleMass_times_V]
  let r : ℕ → ℝ := fun p => (1/(p:ℝ))^(w+1)
  have hr0 : ∀ p∈smallPrimes w, 0≤r p := fun p _ => by dsimp [r]; positivity
  have hrhalf : ∀ p∈smallPrimes w, r p≤(1/2:ℝ)^(w+1) := by
    intro p hp
    have hpR : (2:ℝ)≤(p:ℝ) := by exact_mod_cast (mem_smallPrimes.mp hp).1.two_le
    have hbase : (1:ℝ)/(p:ℝ)≤1/2 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpR
    exact pow_le_pow_left₀ (by positivity) hbase _
  have hr1 : ∀ p∈smallPrimes w, r p≤1 := by
    intro p hp
    exact (hrhalf p hp).trans (pow_le_one₀ (by norm_num) (by norm_num))
  have hcard : (smallPrimes w).card≤w := by
    have h := card_le_card (filter_subset Nat.Prime (Icc 2 w))
    exact h.trans (by simp only [Nat.card_Icc]; omega)
  have hsum : (∑ p∈smallPrimes w, r p)≤(1:ℝ)/2 := by
    calc
      (∑ p∈smallPrimes w, r p) ≤ ∑ _p∈smallPrimes w, (1/2:ℝ)^(w+1) :=
        sum_le_sum hrhalf
      _ = ((smallPrimes w).card:ℝ)*(1/2:ℝ)^(w+1) := by simp
      _ ≤ (w:ℝ)*(1/2:ℝ)^(w+1) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
      _ ≤ (1:ℝ)/2 := by
        have hp : w≤2^w := (Nat.lt_pow_self (by decide : 1<2)).le
        have hpR : (w:ℝ)≤(2:ℝ)^w := by exact_mod_cast hp
        have hmul := mul_le_mul_of_nonneg_right hpR
          (by positivity : (0:ℝ)≤(1/2:ℝ)^(w+1))
        have hid : (2:ℝ)^w*(1/2:ℝ)^(w+1)=1/2 := by
          rw [pow_succ, ← mul_assoc, ← mul_pow]
          norm_num
        rwa [hid] at hmul
  have hprod := one_sub_sum_le_product (smallPrimes w) r hr0 hr1
  dsimp [productComplement, r] at *
  linarith

/-- Finite smooth-number truncation and Markov give the weak Mertens bound.
The exponent cutoff is w, so this proof does not pass to an infinite product. -/
lemma primeTupleMass_le_harmonic (w : ℕ) :
    primeTupleMass (smallPrimes w) w ≤
      2*H (2^(8*(Nat.log 2 w+1))) := by
  classical
  let s := smallPrimes w
  let k := Nat.log 2 w
  let X : ℕ := 2^(8*(k+1))
  let Ω := PrimeExponentTuple s w
  let weight : Ω → ℝ := primeTupleWeight s w
  let height : Ω → ℝ := fun e => Real.log (primeTupleNumber s w e:ℝ)
  let T : ℝ := 8*((k+1:ℕ):ℝ)*Real.log 2
  have hs : ∀ p∈s, Nat.Prime p := fun p hp => (mem_smallPrimes.mp hp).1
  have hT : 0<T := by dsimp [T]; (have := log_two_pos; positivity)
  have hX : 0<X := by dsimp [X]; positivity
  have hlogX : Real.log (X:ℝ)=T := by
    dsimp [X,T]
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    push_cast
    ring
  have hw0 : ∀ e, 0≤weight e := fun e => by dsimp [weight,primeTupleWeight]; positivity
  have hh0 : ∀ e, 0≤height e := by
    intro e
    exact Real.log_nonneg (by exact_mod_cast primeTupleNumber_pos s w hs e)
  have hmoment : (∑ e : Ω, weight e*height e) ≤ (T/2)*(∑ e : Ω, weight e) := by
    have hm := primeTuple_log_moment s w hs
    have hl := weighted_prime_log_le w
    have hz : 0≤primeTupleMass s w := sum_nonneg (fun e _ => hw0 e)
    have hmul := mul_le_mul_of_nonneg_left hl hz
    change (∑ e : Ω, weight e*height e) ≤ primeTupleMass s w * _ at hm
    dsimp [s,k,T,primeTupleMass,weight] at *
    nlinarith
  have hlo := finite_weight_low_mass weight height T hT hw0 hh0 hmoment
  let low : Finset Ω := univ.filter (fun e => height e≤T)
  have hmap : ∀ e∈low, primeTupleNumber s w e∈Icc 1 X := by
    intro e he
    have heT := (mem_filter.mp he).2
    refine mem_Icc.mpr ⟨primeTupleNumber_pos s w hs e, ?_⟩
    by_contra hn
    have hgt : X<primeTupleNumber s w e := by omega
    have hlog := Real.log_lt_log (by exact_mod_cast hX : (0 : ℝ) < (X : ℝ))
      (by exact_mod_cast hgt : (X : ℝ) < (primeTupleNumber s w e : ℝ))
    rw [hlogX] at hlog
    exact (not_lt.mpr heT) hlog
  have hsum : (∑ e∈low, weight e)≤H X := by
    apply sum_le_sum_of_injOn low (Icc 1 X) (primeTupleNumber s w)
      (fun n => 1/(n:ℝ)) hmap
      (fun e he f hf h => primeTupleNumber_injective s w hs h)
      (fun n _ => by positivity)
  change primeTupleMass s w ≤ 2*H X
  change primeTupleMass s w ≤ 2*(∑ e∈low, weight e) at hlo
  linarith

/-- An explicit positive constant; no effective small-cutoff claim is needed. -/
def mertensConstant : ℝ := 4*(1/Real.log 2+16)

lemma mertensConstant_pos : 0 < mertensConstant := by
  dsimp [mertensConstant]
  (have := log_two_pos; positivity)

/-- The lower prime-product bound needed for the packet mean. -/
theorem weak_mertens_lower (w : ℕ) (hw : 2≤w) :
    1/(mertensConstant*Real.log (w:ℝ)) ≤ V w := by
  let k := Nat.log 2 w
  let X : ℕ := 2^(8*(k+1))
  have hw0 : 0<w := by omega
  have hwR : (1:ℝ)<(w:ℝ) := by exact_mod_cast (by omega : 1<w)
  have hlogw : 0<Real.log (w:ℝ) := Real.log_pos hwR
  have hk1 : 1≤k := Nat.log_pos (by decide) hw
  have hlogk := log_two_nat_le_real w hw0
  have hlog2w : Real.log 2≤Real.log (w:ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hw)
  have hXlog : Real.log (X:ℝ)=8*((k+1:ℕ):ℝ)*Real.log 2 := by
    dsimp [X]
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    push_cast
    ring
  have hH : H X ≤ (1/Real.log 2+16)*Real.log (w:ℝ) := by
    have hb := H_le X
    rw [hXlog] at hb
    have hkR : (1:ℝ)≤(k:ℝ) := by exact_mod_cast hk1
    have h1 : (1:ℝ)≤Real.log (w:ℝ)/Real.log 2 :=
      (le_div_iff₀ log_two_pos).mpr (by simpa using hlog2w)
    dsimp [k] at *
    push_cast at hb
    have ht : ((Nat.log 2 w:ℝ)+1)*Real.log 2 ≤ 2*Real.log (w:ℝ) := by
      nlinarith [log_two_pos]
    have heq : (1/Real.log 2)*Real.log (w:ℝ)=Real.log (w:ℝ)/Real.log 2 := by ring
    rw [← heq] at h1
    nlinarith
  have hmass := primeTupleMass_le_harmonic w
  have hprod := primeTupleMass_not_too_small w hw
  have hV := (V_pos w).le
  have hm := mul_le_mul_of_nonneg_right hmass hV
  have hh := mul_le_mul_of_nonneg_right hH hV
  have hden : 0 < mertensConstant*Real.log (w:ℝ) := mul_pos mertensConstant_pos hlogw
  apply (div_le_iff₀ hden).mpr
  dsimp [mertensConstant, X, k] at *
  nlinarith

end
end PrimeAbundance.Analytic
