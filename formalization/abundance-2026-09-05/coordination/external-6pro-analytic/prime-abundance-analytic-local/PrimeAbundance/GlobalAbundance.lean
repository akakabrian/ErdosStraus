/- Assembly of the original quantitative prime-abundance conclusion.
A single delayed interval plus a bounded initial segment avoids a dyadic-union hypothesis. -/
import PrimeAbundance.FiniteTransfer
import PrimeAbundance.PrimeCount

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Classical
open scoped BigOperators Topology
open Finset Filter

namespace PrimeAbundance.Analytic
noncomputable section

def abundanceCoefficient : ℝ := 1/(221184*meanConstant)
def intervalPrefactor : ℝ := 4*varianceConstant+1000
def abundanceBoundConstant : ℝ := 110592*intervalPrefactor

def scaleIndex (N : ℕ) : ℕ := Nat.log 2 N/24
def delayedStart (n : ℕ) : ℕ := 12*(2^n)^8+1

def intervalMultiplicity (n : ℕ) : ℕ :=
  ⌊(n:ℝ)^3/(2*meanConstant*logIndex n)⌋₊

lemma abundanceCoefficient_pos : 0 < abundanceCoefficient := by
  dsimp [abundanceCoefficient]
  (have := meanConstant_pos; positivity)
lemma intervalPrefactor_pos : 0 < intervalPrefactor := by
  dsimp [intervalPrefactor]
  (have := varianceConstant_pos; positivity)
lemma abundanceBoundConstant_pos : 0 < abundanceBoundConstant := by
  dsimp [abundanceBoundConstant]
  (have := intervalPrefactor_pos; positivity)

lemma scaleIndex_lower (N n₀ : ℕ) (hN : 2^(24*n₀) ≤ N) : n₀ ≤ scaleIndex N := by
  have hlog : 24*n₀≤Nat.log 2 N := Nat.le_log_of_pow_le (by decide) hN
  apply (Nat.le_div_iff_mul_le (by decide : 0<24)).mpr
  omega

lemma scaleIndex_power_lower (N : ℕ) (hN : 0 < N) : (2^scaleIndex N)^24 ≤ N := by
  have hmul : 24*scaleIndex N≤Nat.log 2 N := by
    simpa [scaleIndex,mul_comm] using Nat.div_mul_le_self (Nat.log 2 N) 24
  have hp := Nat.pow_le_of_le_log hN.ne' hmul
  simpa [←pow_mul,mul_comm] using hp

lemma scaleIndex_power_upper (N : ℕ) : N < 2^(24*(scaleIndex N+1)) := by
  have hmod := Nat.mod_lt (Nat.log 2 N) (by decide : 0<24)
  have hid := Nat.mod_add_div (Nat.log 2 N) 24
  have hindex : Nat.log 2 N+1≤24*(scaleIndex N+1) := by
    dsimp [scaleIndex]
    omega
  exact (Nat.lt_pow_succ_log_self (b := 2) (by decide) N).trans_le
    (Nat.pow_le_pow_right (by decide) hindex)

lemma self_le_two_pow (n : ℕ) : n ≤ 2^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    have hp : 1 ≤ 2^n := by
      have : 0 < 2^n := pow_pos (by decide) n
      omega
    omega

lemma log_upper_from_index (n p : ℕ) (hn : 1 ≤ n) (hp : 0 < p)
    (hupper : p < 2^(24*(n+1))) : Real.log (p:ℝ) ≤ 48*(n:ℝ) := by
  have hpR : (0:ℝ) < (p:ℝ) := Nat.cast_pos.mpr hp
  have hupperR : (p:ℝ) < ((2^(24*(n+1)):ℕ):ℝ) := Nat.cast_lt.mpr hupper
  have hlog := Real.log_lt_log hpR hupperR
  have hpowlog : Real.log (((2^(24*(n+1)):ℕ):ℝ)) =
      ((24*(n+1):ℕ):ℝ)*Real.log 2 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  rw [hpowlog] at hlog
  have hnR : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hcast : ((24*(n+1):ℕ):ℝ) = 24*((n:ℝ)+1) := by push_cast; ring
  rw [hcast] at hlog
  have hm := mul_le_mul_of_nonneg_left log_two_lt_one.le
    (by positivity : (0:ℝ)≤24*((n:ℝ)+1))
  calc
    Real.log (p:ℝ) ≤ 24*((n:ℝ)+1)*Real.log 2 := hlog.le
    _ ≤ 24*((n:ℝ)+1) := by simpa only [mul_one] using hm
    _ ≤ 48*(n:ℝ) := by nlinarith only [hnR]

lemma log_lower_from_start (n p : ℕ) (hn : 1 ≤ n) (hp : delayedStart n < p) :
    4*(n:ℝ) ≤ Real.log (p:ℝ) := by
  have hpow : (2^n)^8≤p := by
    dsimp [delayedStart] at hp
    omega
  have hpowR : (((2^n)^8:ℕ):ℝ) ≤ (p:ℝ) := Nat.cast_le.mpr hpow
  have hlog := Real.log_le_log (by positivity : (0:ℝ) < (((2^n)^8:ℕ):ℝ)) hpowR
  have hpowlog : Real.log ((((2^n)^8:ℕ):ℝ)) = 8*(n:ℝ)*Real.log 2 := by
    rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, Real.log_pow]
    push_cast
    ring
  rw [hpowlog] at hlog
  have hm := mul_le_mul_of_nonneg_left half_le_log_two (by positivity : (0:ℝ)≤8*(n:ℝ))
  calc
    4*(n:ℝ) ≤ 8*(n:ℝ)*Real.log 2 := by
      convert hm using 1 <;> ring
    _ ≤ Real.log (p:ℝ) := hlog

lemma loglog_lower_from_start (n p : ℕ) (hn : 1 ≤ n) (hp : delayedStart n < p) :
    logIndex n ≤ Real.log (Real.log (p:ℝ)) := by
  have hl := log_lower_from_start n p hn hp
  have hnp : ((n+1:ℕ):ℝ) ≤ Real.log (p:ℝ) := by
    have hnR : (1:ℝ)≤(n:ℝ) := by exact_mod_cast hn
    push_cast
    linarith
  exact Real.log_le_log (by positivity) hnp

/-- The pointwise logarithmic threshold is dominated before taking natural floors. -/
lemma requestedMultiplicity_le_interval (n p : ℕ) (hn : 3 ≤ n)
    (hlower : delayedStart n < p) (hupper : p < 2^(24*(n+1))) :
    requestedMultiplicity abundanceCoefficient p ≤ intervalMultiplicity n := by
  have hn1 : 1≤n := by omega
  have hp0 : 0<p := lt_of_le_of_lt (Nat.zero_le _) hlower
  have hloglo := log_lower_from_start n p hn1 hlower
  have hloghi := log_upper_from_index n p hn1 hp0 hupper
  have hll := loglog_lower_from_start n p hn1 hlower
  have ht0 := logIndex_pos hn1
  have hlog0 : 0 ≤ Real.log (p:ℝ) :=
    (mul_nonneg (by norm_num) (by positivity : (0:ℝ) ≤ (n:ℝ))).trans hloglo
  have hll0 : 0 < Real.log (Real.log (p:ℝ)) := ht0.trans_le hll
  unfold requestedMultiplicity intervalMultiplicity
  apply Nat.floor_mono
  calc
    abundanceCoefficient*(Real.log (p:ℝ))^3/Real.log (Real.log (p:ℝ)) ≤
        abundanceCoefficient*(48*(n:ℝ))^3/Real.log (Real.log (p:ℝ)) := by
      have hcube := pow_le_pow_left₀ hlog0 hloghi 3
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcube abundanceCoefficient_pos.le) hll0.le
    _ ≤ abundanceCoefficient*(48*(n:ℝ))^3/logIndex n :=
      div_le_div_of_nonneg_left (by (have := abundanceCoefficient_pos; positivity)) ht0 hll
    _ = (n:ℝ)^3/(2*meanConstant*logIndex n) := by
      dsimp [abundanceCoefficient]
      field_simp
      ring

lemma intervalMultiplicity_le_mean (n : ℕ) (hn : 1 ≤ n)
    (hmean : (n:ℝ)^3/(meanConstant*logIndex n) ≤ Late.mean (2^n)) :
    (intervalMultiplicity n:ℝ) ≤ Late.mean (2^n)/2 := by
  have ht0 := logIndex_pos hn
  have hdenpos : 0 < 2*meanConstant*logIndex n :=
    mul_pos (mul_pos (by norm_num) meanConstant_pos) ht0
  have hf : (intervalMultiplicity n:ℝ) ≤ (n:ℝ)^3/(2*meanConstant*logIndex n) :=
    Nat.floor_le (by positivity)
  have hid : (n:ℝ)^3/(2*meanConstant*logIndex n)=
      ((n:ℝ)^3/(meanConstant*logIndex n))/2 := by
    field_simp
  rw [hid] at hf
  linarith

/-- Initial bad primes are counted trivially; all later ones inject into the finite interval. -/
lemma badPrimes_card_le_initial_and_offsets (c : ℝ) (N A r : ℕ) (hA : 0 < A)
    (hthreshold : ∀ p:ℕ, A < p → p ≤ N → requestedMultiplicity c p ≤ r) :
    ((badPrimes c N).card:ℝ) ≤ (A:ℝ)+((Late.badOffsets A N r).card:ℝ) := by
  classical
  let S := badPrimes c N
  let lo := S.filter (fun p => p≤A)
  let hi := S.filter (fun p => A<p)
  have hsplit : S.card=lo.card+hi.card := by
    have hset : S=lo∪hi := by
      ext p
      simp only [lo,hi,mem_union,mem_filter]
      constructor
      · intro hpS
        by_cases hpA : p ≤ A
        · exact Or.inl ⟨hpS, hpA⟩
        · exact Or.inr ⟨hpS, Nat.lt_of_not_ge hpA⟩
      · rintro (⟨hpS, _⟩ | ⟨hpS, _⟩) <;> exact hpS
    have hd : Disjoint lo hi := disjoint_left.mpr (by
      intro p hp hq
      have h1 := (mem_filter.mp hp).2
      have h2 := (mem_filter.mp hq).2
      omega)
    rw [hset,card_union_of_disjoint hd]
  have hlo : lo.card≤A := by
    have hsub : lo⊆Icc 1 A := by
      intro p hp
      obtain ⟨hpS,hpA⟩ := mem_filter.mp hp
      have hpi := mem_Icc.mp (mem_filter.mp hpS).1
      exact mem_Icc.mpr ⟨by omega,hpA⟩
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using card_le_card hsub
  let f : hi → Late.badOffsets A N r := fun p =>
    ⟨⟨p.val-A,by
      have hpN := (mem_Icc.mp (mem_filter.mp (mem_filter.mp p.property).1).1).2
      have hpA := (mem_filter.mp p.property).2
      omega⟩,by
      have hpS := (mem_filter.mp p.property).1
      have hpA := (mem_filter.mp p.property).2
      have hpI := mem_Icc.mp (mem_filter.mp hpS).1
      have hpbad := (mem_filter.mp hpS).2
      have heq : A+(p.val-A)=p.val := by omega
      apply mem_filter.mpr
      refine ⟨mem_univ _,?_⟩
      rw [heq]
      refine ⟨hpbad.1,?_⟩
      intro hsol
      exact hpbad.2 (hasAtLeast_mono p.val (requestedMultiplicity c p.val) r (hthreshold p.val hpA hpI.2) hsol)⟩
  have hinj : Function.Injective f := by
    intro p q h
    have hv := congrArg (fun z:Late.badOffsets A N r => z.val.val) h
    dsimp [f] at hv
    have hpA := (mem_filter.mp p.property).2
    have hqA := (mem_filter.mp q.property).2
    apply Subtype.ext
    omega
  have hhi : hi.card≤(Late.badOffsets A N r).card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinj
  have htot : S.card≤A+(Late.badOffsets A N r).card := by omega
  exact_mod_cast htot

lemma delayed_endpoint_bound (n N : ℕ) (hn : 3 ≤ n) (hN : (2^n)^24 ≤ N) :
    (delayedStart n:ℝ)+4*(1+12*((2^n:ℕ):ℝ)^8)^2 ≤
      1000*(N:ℝ)*(logIndex n)^2/(n:ℝ)^3 := by
  have hn0 : (0:ℝ)<(n:ℝ) := by exact_mod_cast (by omega : 0<n)
  have hB1 : (1:ℝ) ≤ ((2^n:ℕ):ℝ) := by
    have hp : 0 < 2^n := pow_pos (by decide) n
    exact_mod_cast (show 1 ≤ 2^n by omega)
  have hB8 : (1:ℝ)≤((2^n:ℕ):ℝ)^8 := one_le_pow₀ hB1
  have hstart : (delayedStart n:ℝ)=1+12*((2^n:ℕ):ℝ)^8 := by
    simp only [delayedStart,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_one,Nat.cast_ofNat]
    ring
  have hA1 : (1:ℝ)≤1+12*((2^n:ℕ):ℝ)^8 :=
    le_add_of_nonneg_right (by positivity)
  have hA : 1+12*((2^n:ℕ):ℝ)^8≤13*((2^n:ℕ):ℝ)^8 := by linarith
  have hA2 := pow_le_pow_left₀ (by positivity : (0:ℝ)≤1+12*((2^n:ℕ):ℝ)^8) hA 2
  have hn3 : n^3≤(2^n)^8 := by
    calc
      n^3≤(2^n)^3 := Nat.pow_le_pow_left (self_le_two_pow n) 3
      _ ≤ (2^n)^8 := Nat.pow_le_pow_right (by positivity) (by decide)
  have hmul : (2^n)^16*n^3≤N := by
    calc
      _ ≤ (2^n)^16*(2^n)^8 := Nat.mul_le_mul_left _ hn3
      _ = (2^n)^24 := by ring
      _ ≤ N := hN
  have hB16 : ((2^n:ℕ):ℝ)^16≤(N:ℝ)/(n:ℝ)^3 := by
    apply (le_div_iff₀ (pow_pos hn0 _)).mpr
    exact_mod_cast hmul
  have hpoly : (1+12*((2^n:ℕ):ℝ)^8)+4*(1+12*((2^n:ℕ):ℝ)^8)^2≤
      845*((2^n:ℕ):ℝ)^16 := by
    have hsq : 1+12*((2^n:ℕ):ℝ)^8≤(1+12*((2^n:ℕ):ℝ)^8)^2 := by nlinarith
    nlinarith
  have htt := one_le_logIndex hn
  have htsq : (1:ℝ)≤(logIndex n)^2 := by nlinarith
  have hscaled := mul_le_mul_of_nonneg_left htsq
    (by positivity : (0:ℝ)≤(N:ℝ)/(n:ℝ)^3)
  rw [hstart]
  calc
    _ ≤ 845*((2^n:ℕ):ℝ)^16 := hpoly
    _ ≤ 845*((N:ℝ)/(n:ℝ)^3) := mul_le_mul_of_nonneg_left hB16 (by norm_num)
    _ ≤ 1000*((N:ℝ)/(n:ℝ)^3)*(logIndex n)^2 := by nlinarith
    _ = _ := by ring

/-- Finite global count at a dyadic analytic index. -/
theorem global_count_at_index (n N : ℕ) (hn : 8 ≤ n)
    (hNlo : (2^n)^24 ≤ N) (hNhi : N < 2^(24*(n+1)))
    (hμ : 0 < Late.mean (2^n))
    (hmean : (n:ℝ)^3/(meanConstant*logIndex n) ≤ Late.mean (2^n))
    (hov : Late.overlap (2^n) ≤ overlapConstant*(n:ℝ)^3) :
    ((badPrimes abundanceCoefficient N).card:ℝ) ≤
      intervalPrefactor*(N:ℝ)*(logIndex n)^2/(n:ℝ)^3 := by
  let A := delayedStart n
  let r := intervalMultiplicity n
  have hn1 : 1 ≤ n := (by decide : 1 ≤ 8).trans hn
  have hn3 : 3 ≤ n := (by decide : 3 ≤ 8).trans hn
  have ht := one_le_logIndex hn3
  have hthreshold : ∀ p:ℕ, A < p → p ≤ N → requestedMultiplicity abundanceCoefficient p ≤ r := by
    intro p hp hpN
    exact requestedMultiplicity_le_interval n p hn3 hp (hpN.trans_lt hNhi)
  have hinit := badPrimes_card_le_initial_and_offsets abundanceCoefficient N A r
    (by dsimp [A, delayedStart]; positivity) hthreshold
  have hfinite := Late.finite_exceptional_bound (2^n) A N r (pow_pos (by decide) n) hμ
    (by dsimp [A, delayedStart]; exact Nat.lt_succ_self _)
    (intervalMultiplicity_le_mean n hn1 hmean)
  have hvariance := normalized_variance_bound n hn1 ht hμ hmean hov
  have hend := delayed_endpoint_bound n N hn3 hNlo
  have hN0 : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
  have hscaled := mul_le_mul_of_nonneg_left hvariance hN0
  have hscaleid : (N:ℝ)*((Late.mean (2^n)+2*Late.overlap (2^n))/(Late.mean (2^n))^2)=
      (N:ℝ)*(Late.mean (2^n)+2*Late.overlap (2^n))/(Late.mean (2^n))^2 := by ring
  rw [hscaleid] at hscaled
  dsimp [A,r,intervalPrefactor] at *
  calc
    _ ≤ (delayedStart n:ℝ)+((Late.badOffsets (delayedStart n) N
        (intervalMultiplicity n)).card:ℝ) := hinit
    _ ≤ (delayedStart n:ℝ)+4*((N:ℝ)*
        (Late.mean (2^n)+2*Late.overlap (2^n))/(Late.mean (2^n))^2+
        (1+12*((2^n:ℕ):ℝ)^8)^2) := add_le_add (le_refl _) hfinite
    _ = ((delayedStart n:ℝ)+4*(1+12*((2^n:ℕ):ℝ)^8)^2)+
        4*((N:ℝ)*(Late.mean (2^n)+2*Late.overlap (2^n))/(Late.mean (2^n))^2) := by ring
    _ ≤ 1000*(N:ℝ)*(logIndex n)^2/(n:ℝ)^3+
        4*((N:ℝ)*(Late.mean (2^n)+2*Late.overlap (2^n))/(Late.mean (2^n))^2) :=
      add_le_add hend (le_refl _)
    _ ≤ 1000*(N:ℝ)*(logIndex n)^2/(n:ℝ)^3+
        4*((N:ℝ)*(varianceConstant*(logIndex n)^2/(n:ℝ)^3)) :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hscaled (by norm_num : (0:ℝ) ≤ 4))
    _ = (4*varianceConstant+1000)*(N:ℝ)*(logIndex n)^2/(n:ℝ)^3 := by ring

lemma scale_comparison (n N : ℕ) (hn : 3 ≤ n)
    (hNlo : (2^n)^24 ≤ N) (hNhi : N < 2^(24*(n+1))) :
    (N:ℝ)*(logIndex n)^2/(n:ℝ)^3 ≤ 110592*originalExceptionalScale N := by
  have hn1 : 1≤n := (by decide : 1 ≤ 3).trans hn
  have hnpos : 0 < n := (by decide : 0 < 3).trans_le hn
  have hnR : (0:ℝ)<(n:ℝ) := Nat.cast_pos.mpr hnpos
  have hpowpos : 0 < (2^n)^24 := pow_pos (pow_pos (by decide) n) 24
  have hNpos : 0<N := hpowpos.trans_le hNlo
  have hlogU := log_upper_from_index n N hn1 hNpos hNhi
  have hlogL : 12*(n:ℝ) ≤ Real.log (N:ℝ) := by
    have hNloR : (((2^n)^24:ℕ):ℝ) ≤ (N:ℝ) := Nat.cast_le.mpr hNlo
    have h := Real.log_le_log (by positivity : (0:ℝ) < (((2^n)^24:ℕ):ℝ)) hNloR
    have hpowlog : Real.log ((((2^n)^24:ℕ):ℝ)) = 24*(n:ℝ)*Real.log 2 := by
      rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, Real.log_pow]
      push_cast
      ring
    rw [hpowlog] at h
    have hm := mul_le_mul_of_nonneg_left half_le_log_two (by positivity : (0:ℝ)≤24*(n:ℝ))
    calc
      12*(n:ℝ) ≤ 24*(n:ℝ)*Real.log 2 := by
        convert hm using 1 <;> ring
      _ ≤ Real.log (N:ℝ) := h
  have hlogpos : 0 < Real.log (N:ℝ) := by
    exact (mul_pos (by norm_num) hnR).trans_le hlogL
  have hll : logIndex n ≤ Real.log (Real.log (N:ℝ)) := by
    apply Real.log_le_log (by positivity)
    have hnR1 : (1:ℝ)≤(n:ℝ) := by exact_mod_cast hn1
    push_cast
    nlinarith only [hlogL, hnR1]
  have ht := one_le_logIndex hn
  have hll1 : 1 ≤ Real.log (Real.log (N:ℝ)) := ht.trans hll
  have hnum : (logIndex n)^2 ≤ (Real.log (Real.log (N:ℝ)))^3 := by
    have hsq := pow_le_pow_left₀ (zero_le_one.trans ht) hll 2
    have hcube : (Real.log (Real.log (N:ℝ)))^2 ≤ (Real.log (Real.log (N:ℝ)))^3 := by
      nlinarith only [hll1, sq_nonneg (Real.log (Real.log (N:ℝ)))]
    exact hsq.trans hcube
  have hden : 1/(n:ℝ)^3 ≤ 110592/(Real.log (N:ℝ))^3 := by
    apply (div_le_div_iff₀ (pow_pos hnR _) (pow_pos hlogpos _)).mpr
    have hp := pow_le_pow_left₀ hlogpos.le hlogU 3
    convert hp using 1 <;> ring
  have hprod := mul_le_mul hnum hden (by positivity) (by positivity)
  have hscaled := mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg N)
  calc
    (N:ℝ)*(logIndex n)^2/(n:ℝ)^3 =
        (N:ℝ)*((logIndex n)^2*(1/(n:ℝ)^3)) := by ring
    _ ≤ (N:ℝ)*((Real.log (Real.log (N:ℝ)))^3*
        (110592/(Real.log (N:ℝ))^3)) := hscaled
    _ = 110592*originalExceptionalScale N := by
      dsimp [originalExceptionalScale]
      ring

/-- The original exceptional-count rate, with concrete positive constants and no analytic premises. -/
theorem quantitative_abundance :
    ∃ N₀:ℕ, 16 ≤ N₀ ∧ ∀ N:ℕ, N₀ ≤ N →
      ((badPrimes abundanceCoefficient N).card:ℝ) ≤
        abundanceBoundConstant*originalExceptionalScale N := by
  obtain ⟨n₀,hn₀,hest⟩ := analytic_bounds
  let N₀ := 2^(24*n₀)
  have hN₀ : 16≤N₀ := by
    have h := Nat.pow_le_pow_right (by decide : 1≤2) (show 4≤24*n₀ by omega)
    simpa [N₀] using h
  refine ⟨N₀,hN₀,?_⟩
  intro N hN
  let n := scaleIndex N
  have hn0 : n₀≤n := scaleIndex_lower N n₀ hN
  have hn8 : 8≤n := hn₀.trans hn0
  have hN₀pos : 0 < N₀ := by
    dsimp [N₀]
    exact pow_pos (by decide) _
  have hNp : 0<N := hN₀pos.trans_le hN
  have hNlo := scaleIndex_power_lower N hNp
  have hNhi := scaleIndex_power_upper N
  obtain ⟨ht,hμ,hmean,hov⟩ := hest n hn0
  have hcount := global_count_at_index n N hn8 hNlo hNhi hμ hmean hov
  have hcomp := scale_comparison n N ((by decide : 3 ≤ 8).trans hn8) hNlo hNhi
  have hscaled := mul_le_mul_of_nonneg_left hcomp intervalPrefactor_pos.le
  apply hcount.trans
  dsimp [abundanceBoundConstant]
  convert hscaled using 1 <;> ring

/-- The rate tends to zero after normalization by an elementary prime-count lower bound. -/
lemma loglog_cube_over_log_square_tendsto :
    Tendsto (fun N:ℕ => (Real.log (Real.log (N:ℝ)))^3/(Real.log (N:ℝ))^2)
      atTop (nhds (0:ℝ)) := by
  have ht : Tendsto (fun N:ℕ => Real.log (N:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  let k : ℕ := 3
  let j : ℕ := 2
  have h := (_root_.isLittleO_log_rpow_rpow_atTop (k:ℝ)
    (show (0:ℝ)<(j:ℝ) by norm_num [j])).tendsto_div_nhds_zero
  have hc := h.comp ht
  change Tendsto (fun N : ℕ =>
    (Real.log (Real.log (N:ℝ)))^(k:ℝ)/(Real.log (N:ℝ))^(j:ℝ)) atTop (nhds (0:ℝ)) at hc
  have hc' : Tendsto (fun N : ℕ =>
      (Real.log (Real.log (N:ℝ)))^k/(Real.log (N:ℝ))^j) atTop (nhds (0:ℝ)) := by
    simpa only [Real.rpow_natCast] using hc
  simpa only [k, j] using hc'

/-- Relative prime density, not merely an algebraic comparison of logarithms. -/
theorem relative_density :
    Tendsto (fun N:ℕ => ((badPrimes abundanceCoefficient N).card:ℝ)/((primesUpTo N).card:ℝ))
      atTop (nhds (0:ℝ)) := by
  obtain ⟨N₀,hN₀,hbound⟩ := quantitative_abundance
  have hupper : ∀ᶠ N:ℕ in atTop,
      ((badPrimes abundanceCoefficient N).card:ℝ)/((primesUpTo N).card:ℝ) ≤
        6*abundanceBoundConstant*(Real.log (Real.log (N:ℝ)))^3/(Real.log (N:ℝ))^2 := by
    filter_upwards [eventually_ge_atTop N₀] with N hN
    have h16 : 16≤N := hN₀.trans hN
    have hlog : 0 < Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    have hNpos : (0:ℝ)<(N:ℝ) := by positivity
    have hp := primeCount_lower N h16
    have hp0 := primeCount_pos N h16
    have hbad := hbound N hN
    have hnumb : 0≤abundanceBoundConstant*originalExceptionalScale N :=
      (show (0:ℝ)≤((badPrimes abundanceCoefficient N).card:ℝ) by positivity).trans hbad
    calc
      _ ≤ (abundanceBoundConstant*originalExceptionalScale N)/((primesUpTo N).card:ℝ) :=
        div_le_div_of_nonneg_right hbad hp0.le
      _ ≤ (abundanceBoundConstant*originalExceptionalScale N)/((N:ℝ)/(6*Real.log (N:ℝ))) :=
        div_le_div_of_nonneg_left hnumb (by positivity) hp
      _ = _ := by
        unfold originalExceptionalScale
        have hNne := hNpos.ne'
        have hlogne := hlog.ne'
        field_simp
  have hlim : Tendsto (fun N:ℕ =>
      6*abundanceBoundConstant*(Real.log (Real.log (N:ℝ)))^3/(Real.log (N:ℝ))^2)
      atTop (nhds (0:ℝ)) := by
    simpa only [mul_zero,mul_div_assoc] using
      loglog_cube_over_log_square_tendsto.const_mul (6*abundanceBoundConstant)
  exact squeeze_zero' (Eventually.of_forall (fun N => by positivity)) hupper hlim

end
end PrimeAbundance.Analytic
