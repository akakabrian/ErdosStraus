/- Actual eventual analytic estimates, proved from the finite estimates.
No mean/overlap estimate is a premise of the public theorems in this module. -/
import PrimeAbundance.Overlap
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
open scoped Classical
open scoped BigOperators Topology
open Finset Filter

namespace PrimeAbundance.Analytic
noncomputable section

abbrev dyadicCutoff (n : ℕ) : ℕ := Late.cutoff ((2^n)^8)
def logIndex (n : ℕ) : ℝ := Real.log ((n+1:ℕ):ℝ)
def meanConstant : ℝ := 307200*mertensConstant
def overlapConstant : ℝ := 2^34
def varianceConstant : ℝ := meanConstant+2*overlapConstant*meanConstant^2

lemma meanConstant_pos : 0 < meanConstant := by
  dsimp [meanConstant]
  exact mul_pos (by norm_num) mertensConstant_pos
lemma overlapConstant_pos : 0 < overlapConstant := by norm_num [overlapConstant]
lemma varianceConstant_pos : 0 < varianceConstant := by
  dsimp [varianceConstant]
  exact add_pos meanConstant_pos (mul_pos (mul_pos (by norm_num) overlapConstant_pos)
    (pow_pos meanConstant_pos 2))

lemma half_le_log_two : (1:ℝ)/2≤Real.log 2 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<(2:ℝ)⁻¹)
  rw [Real.log_inv] at h
  norm_num at h
  linarith

lemma logIndex_nonneg (n : ℕ) : 0≤logIndex n := by
  apply Real.log_nonneg
  exact_mod_cast (by omega : 1 ≤ n+1)

lemma logIndex_pos {n : ℕ} (hn : 1≤n) : 0<logIndex n := by
  apply Real.log_pos
  exact_mod_cast (by omega : 1<n+1)

lemma half_le_logIndex {n : ℕ} (hn : 1≤n) : (1:ℝ)/2≤logIndex n := by
  exact half_le_log_two.trans (Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2≤n+1)))

lemma one_le_logIndex {n : ℕ} (hn : 3≤n) : 1≤logIndex n := by
  have h4 : (1:ℝ)≤Real.log 4 := by
    have he : Real.log 4=2*Real.log 2 := by
      rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
      norm_num
    rw [he]
    linarith [half_le_log_two]
  exact h4.trans (Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 4≤n+1)))

lemma log_dyadic_cutoff_base (n : ℕ) :
    Real.log (((2^n)^8:ℕ):ℝ)=8*(n:ℝ)*Real.log 2 := by
  rw [Nat.cast_pow,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow,Real.log_pow]
  norm_num
  ring

lemma dyadicCutoff_lower (n : ℕ) : (4*n)^100≤dyadicCutoff n := by
  unfold dyadicCutoff Late.cutoff
  apply Nat.le_floor
  rw [log_dyadic_cutoff_base]
  have hbase : ((4*n:ℕ):ℝ) ≤ (8*(n:ℝ)*Real.log 2) := by
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left half_le_log_two (by positivity : (0:ℝ)≤8*(n:ℝ))]
  exact_mod_cast pow_le_pow_left₀ (by positivity : (0:ℝ)≤((4*n:ℕ):ℝ)) hbase 100

lemma dyadicCutoff_ge_two {n : ℕ} (hn : 1≤n) : 2≤dyadicCutoff n := by
  have h : 2≤(4*n)^100 := by
    have hb : 2≤4*n := by omega
    have hpow : 4*n≤(4*n)^100 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1≤4*n) (by decide : 1≤100)
    exact hb.trans hpow
  exact h.trans (dyadicCutoff_lower n)

lemma dyadicCutoff_upper (n : ℕ) : dyadicCutoff n≤(8*n)^100 := by
  unfold dyadicCutoff Late.cutoff
  rw [log_dyadic_cutoff_base]
  have hbase : 8*(n:ℝ)*Real.log 2≤((8*n:ℕ):ℝ) := by
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left log_two_lt_one.le (by positivity : (0:ℝ)≤8*(n:ℝ))]
  have hpow := pow_le_pow_left₀ (by (have := log_two_pos; positivity) : (0:ℝ)≤8*(n:ℝ)*Real.log 2) hbase 100
  have hf := Nat.floor_mono hpow
  calc
    _ ≤ ⌊(((8*n:ℕ):ℝ)^100)⌋₊ := hf
    _ = (8*n)^100 := by
      simpa only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] using
        (Nat.floor_natCast ((8*n)^100) : ⌊(((8*n)^100:ℕ):ℝ)⌋₊=(8*n)^100)

lemma dyadicCutoff_log_bound {n : ℕ} (hn : 1≤n) :
    Real.log (dyadicCutoff n:ℝ)≤400*logIndex n := by
  have hw := dyadicCutoff_ge_two hn
  have hbig : (8*n:ℕ)≤(n+1)^4 := by
    have hnonneg : 0≤n-1 := Nat.zero_le _
    have hn2 : n≤n^2 := by nlinarith
    nlinarith [Nat.zero_le (n^4),Nat.zero_le (n^3)]
  have hw0 : (0:ℝ)<(dyadicCutoff n:ℝ) := by positivity
  calc
    _ ≤ Real.log (((8*n)^100:ℕ):ℝ) :=
      Real.log_le_log hw0 (by exact_mod_cast dyadicCutoff_upper n)
    _ = 100*Real.log ((8*n:ℕ):ℝ) := by rw [Nat.cast_pow,Real.log_pow]; norm_num
    _ ≤ 100*Real.log (((n+1)^4:ℕ):ℝ) := by gcongr
    _ = 400*logIndex n := by
      rw [Nat.cast_pow,Real.log_pow]
      dsimp [logIndex]
      norm_num
      ring

lemma rayCutoff_dyadic_le (n : ℕ) : Late.rayCutoff (2^n)≤n^2+2 := by
  unfold Late.rayCutoff
  apply Nat.add_le_add_right _ 2
  rw [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
  have hbase : (n:ℝ)*Real.log 2≤(n:ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left log_two_lt_one.le (by positivity : (0:ℝ)≤(n:ℝ))]
  have hp := pow_le_pow_left₀ (by (have := log_two_pos; positivity) : (0:ℝ)≤(n:ℝ)*Real.log 2) hbase 2
  calc
    _ ≤ ⌊(((n:ℕ):ℝ)^2)⌋₊ := Nat.floor_mono hp
    _ = n^2 := by
      simpa only [Nat.cast_pow] using
        (Nat.floor_natCast (n^2) : ⌊((n^2:ℕ):ℝ)⌋₊=n^2)

/-- Logarithmic squares are eventually smaller than any prescribed multiple of n+1. -/
lemma logIndex_sq_small (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n:ℕ in atTop,(logIndex n)^2≤ε*((n+1:ℕ):ℝ) := by
  have ht : Tendsto (fun n:ℕ => ((n+1:ℕ):ℝ)) atTop atTop := by
    simpa only [Nat.cast_add,Nat.cast_one] using
      (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1:ℝ))))
  have h := (_root_.isLittleO_log_rpow_rpow_atTop (2:ℝ) (by norm_num : (0:ℝ)<1)).comp_tendsto ht
  have hb := h.bound hε
  filter_upwards [hb] with n hn
  simp only [Function.comp_apply,Real.rpow_natCast,Real.rpow_one] at hn
  rw [Real.rpow_two] at hn
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ)≤((n+1:ℕ):ℝ))] at hn
  simpa only [logIndex] using hn

lemma sieveLength_log_bound {n : ℕ} (hn : 1≤n) :
    Real.log (sieveLength (dyadicCutoff n):ℝ)≤3000000*(logIndex n)^2 := by
  let w := dyadicCutoff n
  let t := logIndex n
  have hw := dyadicCutoff_ge_two hn
  have hw0 : 0<w := by dsimp [w]; omega
  have hl : 0 < Real.log (w:ℝ) := Real.log_pos (by exact_mod_cast (show 1<w by dsimp [w]; omega))
  have hlog := dyadicCutoff_log_bound hn
  have hk : (Nat.log 2 w:ℝ)≤2*Real.log (w:ℝ) := by
    have h := log_two_nat_le_real w hw0
    have hk0 : (0:ℝ)≤(Nat.log 2 w:ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left half_le_log_two hk0]
  have hlev : ((sieveLevel w+2:ℕ):ℝ)≤16*Real.log (w:ℝ)+10 := by
    dsimp [sieveLevel]
    push_cast
    linarith
  have hlog4 : Real.log 4≤2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
    norm_num
    linarith [log_two_lt_one]
  have heq : Real.log (sieveLength w:ℝ)=Real.log 4+((sieveLevel w+2:ℕ):ℝ)*Real.log (w:ℝ) := by
    unfold sieveLength
    rw [Nat.cast_mul,Nat.cast_pow,Real.log_mul (by norm_num) (by positivity),Real.log_pow]
    norm_num
  rw [heq]
  have ht : (1:ℝ)/2≤t := half_le_logIndex hn
  have hmul := mul_le_mul_of_nonneg_right hlev hl.le
  have hsq := pow_le_pow_left₀ hl.le hlog 2
  dsimp [w,t] at *
  nlinarith [sq_nonneg (logIndex n-1/2)]

lemma sieveLength_eventually :
    ∀ᶠ n:ℕ in atTop,sieveLength (dyadicCutoff n)≤(2^n)^4 := by
  filter_upwards [logIndex_sq_small (1/6000000) (by norm_num),eventually_ge_atTop 1] with n hsmall hn
  have hlog := sieveLength_log_bound hn
  have hlen0 : 0<sieveLength (dyadicCutoff n) := by
    have hw := dyadicCutoff_ge_two hn
    unfold sieveLength
    positivity
  have hN : ((n+1:ℕ):ℝ)≤2*(n:ℝ) := by exact_mod_cast (by omega : n+1≤2*n)
  have hlogN : Real.log (((2^n)^4:ℕ):ℝ)=4*(n:ℝ)*Real.log 2 := by
    rw [Nat.cast_pow,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow,Real.log_pow]
    norm_num
    ring
  have hle : Real.log (sieveLength (dyadicCutoff n):ℝ)≤Real.log (((2^n)^4:ℕ):ℝ) := by
    rw [hlogN]
    nlinarith [mul_le_mul_of_nonneg_left half_le_log_two (by positivity : (0:ℝ)≤4*(n:ℝ))]
  exact_mod_cast (Real.log_le_log_iff (by exact_mod_cast hlen0) (by positivity)).mp hle

lemma rayMass_dyadic_eventually :
    ∀ᶠ n:ℕ in atTop,(n:ℝ)^2/32≤rayMass (n^2+2) (2^n) := by
  filter_upwards [logIndex_sq_small (1/2048) (by norm_num),eventually_ge_atTop 8] with n hsmall hn
  have hnt : (1:ℝ)≤(n:ℝ) := by exact_mod_cast (by omega : 1≤n)
  have ht := half_le_logIndex (by omega : 1≤n)
  have htlin : logIndex n≤(n:ℝ)/512 := by
    have hN : ((n+1:ℕ):ℝ)≤2*(n:ℝ) := by exact_mod_cast (by omega : n+1≤2*n)
    nlinarith
  have hB : 1≤2^n := Nat.one_le_two_pow
  have hbase := rayMass_truncation (n^2+2) (2^n) hB
  have hHlo : (n:ℝ)/2≤H (2^n) := by
    have h := log_le_H (2^n) (by positivity)
    rw [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow] at h
    nlinarith [mul_le_mul_of_nonneg_left half_le_log_two (by positivity : (0:ℝ)≤(n:ℝ))]
  have hHhi : H (2^n)≤2*(n:ℝ) := by
    have h := harmonic_dyadic_le n
    nlinarith
  have hK : H (n^2+2-1)≤4*logIndex n := by
    have h := H_le (n^2+1)
    push_cast at h
    have hpow : n^2+1≤(n+1)^2 := by nlinarith
    have hpowR : ((n^2+1:ℕ):ℝ)≤(((n+1)^2:ℕ):ℝ) := by exact_mod_cast hpow
    have hlog := Real.log_le_log (by positivity : (0:ℝ)<((n^2+1:ℕ):ℝ)) hpowR
    rw [Nat.cast_pow,Real.log_pow] at hlog
    have he : n^2+2-1=n^2+1 := by omega
    rw [he]
    dsimp [logIndex] at ht ⊢
    norm_num at hlog
    change H (n^2+1)≤4*Real.log ((n+1:ℕ):ℝ)
    calc
      H (n^2+1)≤1+Real.log ((n:ℝ)^2+1) := h
      _ ≤ 1+2*Real.log ((n+1:ℕ):ℝ) := by
        simpa only [Nat.cast_add, Nat.cast_one, add_comm] using add_le_add_left hlog 1
      _ ≤ 4*Real.log ((n+1:ℕ):ℝ) := by nlinarith
  have hmul := mul_le_mul hK hHhi (H_nonneg _) (by positivity : (0:ℝ)≤4*logIndex n)
  have hs := pow_le_pow_left₀ (by positivity : (0:ℝ)≤(n:ℝ)/2) hHlo 2
  have hntR : (8:ℝ)≤(n:ℝ) := by exact_mod_cast hn
  nlinarith

/-- The required lower mean, for the concrete packet family and its actual cutoff. -/
theorem mean_dyadic_eventually :
    ∀ᶠ n:ℕ in atTop,(n:ℝ)^3/(meanConstant*logIndex n)≤Late.mean (2^n) := by
  filter_upwards [sieveLength_eventually,rayMass_dyadic_eventually,eventually_ge_atTop 8] with n hlen hmass hn
  have hn1 : 1≤n := by omega
  have hw := dyadicCutoff_ge_two hn1
  have hV0 := (V_pos (dyadicCutoff n)).le
  have hfinite := mean_dyadic_lower_finite n (n^2+2) hn1 (rayCutoff_dyadic_le n) hw hlen
  have hm := mul_le_mul_of_nonneg_left hmass
    (by positivity : (0:ℝ)≤(n:ℝ)*V (dyadicCutoff n)/24)
  have hV := weak_mertens_lower (dyadicCutoff n) hw
  have hlog := dyadicCutoff_log_bound hn1
  have ht0 := logIndex_pos hn1
  have hl0 : 0 < Real.log (dyadicCutoff n:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1<dyadicCutoff n))
  have hV' : 1/(400*mertensConstant*logIndex n)≤V (dyadicCutoff n) := by
    apply (one_div_le_one_div_of_le (mul_pos mertensConstant_pos hl0) ?_).trans hV
    nlinarith [mul_le_mul_of_nonneg_left hlog mertensConstant_pos.le]
  have hscaled := mul_le_mul_of_nonneg_left hV' (by positivity : (0:ℝ)≤(n:ℝ)^3/768)
  have hid : (n:ℝ)^3/(meanConstant*logIndex n)=
      ((n:ℝ)^3/768)*(1/(400*mertensConstant*logIndex n)) := by
    dsimp [meanConstant]
    field_simp
    ring
  rw [hid]
  nlinarith

/-- No full-family overlap estimate is invoked. This bounds Late.overlap directly. -/
theorem overlap_dyadic_bound (n : ℕ) (hn : 3≤n) :
    Late.overlap (2^n)≤overlapConstant*(n:ℝ)^3 := by
  have hn1 : 1≤n := by omega
  have hw := dyadicCutoff_ge_two hn1
  have hfinite := overlap_dyadic_finite n hn hw
  have hwn : n^100≤dyadicCutoff n :=
    (Nat.pow_le_pow_left (by omega : n≤4*n) 100).trans (dyadicCutoff_lower n)
  have hn11 : (n+1)^11≤2048*dyadicCutoff n := by
    calc
      (n+1)^11≤(2*n)^11 := Nat.pow_le_pow_left (by omega) 11
      _ = 2048*n^11 := by rw [mul_pow]; norm_num
      _ ≤ 2048*n^100 := Nat.mul_le_mul_left 2048 (Nat.pow_le_pow_right hn1 (by decide))
      _ ≤ 2048*dyadicCutoff n := Nat.mul_le_mul_left 2048 hwn
  have hratio : ((n+1:ℕ):ℝ)^11/(dyadicCutoff n:ℝ)≤2048 := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<(dyadicCutoff n:ℝ))).mpr
    exact_mod_cast hn11
  have hcube : ((n+1:ℕ):ℝ)^3≤8*(n:ℝ)^3 := by
    have h := Nat.pow_le_pow_left (by omega : n+1≤2*n) 3
    have hR : (((n+1)^3:ℕ):ℝ)≤(((2*n)^3:ℕ):ℝ) := by exact_mod_cast h
    norm_num [mul_pow] at hR
    simpa only [Nat.cast_add, Nat.cast_one] using hR
  have hn3 : (1:ℝ)≤(n:ℝ)^3 := by exact_mod_cast (one_le_pow₀ hn1)
  have hfirst := mul_le_mul_of_nonneg_left hcube (by norm_num : (0:ℝ)≤1536)
  have hsecond := mul_le_mul_of_nonneg_left hratio (by norm_num : (0:ℝ)≤131072)
  have hratioTerm : 131072*((n+1:ℕ):ℝ)^11/(dyadicCutoff n:ℝ)≤131072*2048 := by
    calc
      _ = 131072*(((n+1:ℕ):ℝ)^11/(dyadicCutoff n:ℝ)) := by ring
      _ ≤ _ := hsecond
  have hgrow : (131072*2048:ℝ)≤(131072*2048)*(n:ℝ)^3 := by nlinarith
  have hsum : 1536*((n+1:ℕ):ℝ)^3+
      131072*((n+1:ℕ):ℝ)^11/(dyadicCutoff n:ℝ)≤
      (1536*8+131072*2048)*(n:ℝ)^3 := by
    calc
      _ ≤ 1536*(8*(n:ℝ)^3)+(131072*2048)*(n:ℝ)^3 :=
        add_le_add hfirst (hratioTerm.trans hgrow)
      _ = (1536*8+131072*2048)*(n:ℝ)^3 := by ring
  have hconst : (1536*8+131072*2048:ℝ)≤2^34 := by norm_num
  have hfinal := mul_le_mul_of_nonneg_right hconst (by positivity : (0:ℝ)≤(n:ℝ)^3)
  exact hfinite.trans (hsum.trans (by simpa [overlapConstant] using hfinal))

/-- Quantified analytic output. Neither lower mean nor upper overlap is an input. -/
theorem analytic_bounds :
    ∃ n₀:ℕ,8≤n₀ ∧ ∀ n:ℕ,n₀≤n →
      1≤logIndex n ∧ 0<Late.mean (2^n) ∧
      (n:ℝ)^3/(meanConstant*logIndex n)≤Late.mean (2^n) ∧
      Late.overlap (2^n)≤overlapConstant*(n:ℝ)^3 := by
  have h := mean_dyadic_eventually
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp h
  refine ⟨max n₀ 8,le_max_right _ _,?_⟩
  intro n hn
  have hn8 : 8≤n := (le_max_right _ _).trans hn
  have hn0 : n₀≤n := (le_max_left _ _).trans hn
  have hm := hn₀ n hn0
  have hpos : (0:ℝ)<(n:ℝ)^3/(meanConstant*logIndex n) :=
    div_pos (pow_pos (by exact_mod_cast (by omega : 0<n)) _) (mul_pos meanConstant_pos (logIndex_pos (by omega)))
  exact ⟨one_le_logIndex (by omega),hpos.trans_le hm,hm,overlap_dyadic_bound n (by omega)⟩

/-- Normalize the exact variance expression, rather than replacing it by an assumed rate. -/
lemma normalized_variance_bound (n : ℕ) (hn : 1≤n)
    (ht : 1≤logIndex n) (hμ : 0<Late.mean (2^n))
    (hmean : (n:ℝ)^3/(meanConstant*logIndex n)≤Late.mean (2^n))
    (hov : Late.overlap (2^n)≤overlapConstant*(n:ℝ)^3) :
    (Late.mean (2^n)+2*Late.overlap (2^n))/(Late.mean (2^n))^2≤
      varianceConstant*(logIndex n)^2/(n:ℝ)^3 := by
  let μ := Late.mean (2^n)
  let overlapValue := Late.overlap (2^n)
  have hnR : (0:ℝ)<(n:ℝ) := by exact_mod_cast (by omega : 0<n)
  have htR : 0<logIndex n := by linarith
  have hden : 0 < meanConstant*logIndex n := mul_pos meanConstant_pos htR
  have hinv : 1/μ ≤ meanConstant*logIndex n/(n:ℝ)^3 := by
    have h := one_div_le_one_div_of_le (div_pos (pow_pos hnR _) hden) hmean
    simpa only [one_div_div] using h
  have hsquare : (1/μ)^2≤(meanConstant*logIndex n/(n:ℝ)^3)^2 :=
    pow_le_pow_left₀ (by positivity) hinv 2
  have hoverlap := Late.overlap_nonneg (2^n)
  have hprod := mul_le_mul hov hsquare (by positivity : (0:ℝ)≤(1/μ)^2)
    (mul_nonneg overlapConstant_pos.le
      (pow_nonneg (by positivity : (0:ℝ)≤(n:ℝ)) 3))
  have hid : (μ+2*overlapValue)/μ^2=1/μ+2*(overlapValue*(1/μ)^2) := by
    have hμ0 : μ≠0 := hμ.ne'
    field_simp
  have hright : overlapConstant*(n:ℝ)^3*(meanConstant*logIndex n/(n:ℝ)^3)^2=
      overlapConstant*meanConstant^2*(logIndex n)^2/(n:ℝ)^3 := by
    have hn0 := hnR.ne'
    field_simp
  rw [hid]
  rw [hright] at hprod
  have ht2 : logIndex n≤(logIndex n)^2 := by nlinarith
  have hlinear : meanConstant*logIndex n/(n:ℝ)^3≤
      meanConstant*(logIndex n)^2/(n:ℝ)^3 := by
    apply div_le_div_of_nonneg_right
    exact mul_le_mul_of_nonneg_left ht2 meanConstant_pos.le
    positivity
  calc
    1/μ+2*(overlapValue*(1/μ)^2)≤
        meanConstant*logIndex n/(n:ℝ)^3+
          2*(overlapConstant*meanConstant^2*(logIndex n)^2/(n:ℝ)^3) :=
      add_le_add hinv (mul_le_mul_of_nonneg_left hprod (by norm_num))
    _ ≤ meanConstant*(logIndex n)^2/(n:ℝ)^3+
          2*(overlapConstant*meanConstant^2*(logIndex n)^2/(n:ℝ)^3) :=
      add_le_add_left hlinear _
    _ = varianceConstant*(logIndex n)^2/(n:ℝ)^3 := by
      dsimp [varianceConstant]
      ring

end
end PrimeAbundance.Analytic
