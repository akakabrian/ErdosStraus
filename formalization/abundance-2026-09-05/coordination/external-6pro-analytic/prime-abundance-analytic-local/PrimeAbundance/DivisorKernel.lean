/- Weighted gcd kernel on delayed scales. Full divisors, including prime powers. -/
import PrimeAbundance.ScaleSums
import PrimeAbundance.DivisorMoments

set_option autoImplicit false
open scoped Classical
open scoped BigOperators
open Finset

namespace PrimeAbundance.Analytic
noncomputable section

def linearQ (c u : ℕ) : ℕ := c*u-1

def gcdKernel (c L T : ℕ) : ℝ :=
  ∑ u∈Ioc L T, ∑ v∈Ioc u T,
    (Nat.gcd (linearQ c u) (linearQ c v):ℝ)/
      ((linearQ c u:ℝ)*(linearQ c v:ℝ))

lemma linearQ_pos {c u : ℕ} (hc : 2≤c) (hu : 0<u) : 0<linearQ c u := by
  unfold linearQ
  have hlarge : 2≤c*u := by nlinarith
  omega

lemma linearQ_cast {c u : ℕ} (hc : 2≤c) (hu : 0<u) :
    (linearQ c u:ℝ)=(c:ℝ)*(u:ℝ)-1 := by
  have h : 1≤c*u := by nlinarith
  simp [linearQ,Nat.cast_sub h]

lemma linearQ_half {c u : ℕ} (hc : 2≤c) (hu : 0<u) :
    (c:ℝ)*(u:ℝ)/2≤(linearQ c u:ℝ) := by
  rw [linearQ_cast hc hu]
  have h : (2:ℝ)≤(c:ℝ)*(u:ℝ) := by exact_mod_cast (by nlinarith : 2≤c*u)
  linarith

/-- Divisor pairing as an actual injection into small divisors times two signs. -/
lemma tau_le_twice_small_divisors (q U : ℕ) (hq : 0<q) (hqU : q≤U^2) :
    tau q≤2*((Icc 1 U).filter (fun d => d∣q)).card := by
  classical
  let s := (Icc 1 U).filter (fun d => d∣q)
  let f : ℕ → ℕ × Bool := fun d => (if d≤U then d else q/d, decide (d≤U))
  have hmap : ∀ d∈q.divisors,f d∈s.product univ := by
    intro d hd
    have hdq := (Nat.mem_divisors.mp hd).1
    have hd0 : 0<d := Nat.pos_of_dvd_of_pos hdq hq
    have hdle := Nat.le_of_dvd hq hdq
    have hprod : d*(q/d)=q := by nlinarith [Nat.div_mul_cancel hdq]
    have hquot : 0<q/d := Nat.div_pos hdle hd0
    apply mem_product.mpr
    refine ⟨?_,mem_univ _⟩
    dsimp [f]
    by_cases h : d≤U
    · simp only [if_pos h]
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hd0,h⟩,hdq⟩
    · simp only [if_neg h]
      have hqU' : q/d≤U := by
        by_contra hz
        have hdU : U+1≤d := by omega
        have hqU : U+1≤q/d := by omega
        have hm := Nat.mul_le_mul hdU hqU
        nlinarith [hprod]
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hquot,hqU'⟩,Nat.div_dvd_of_dvd hdq⟩
  have hinj : Set.InjOn f q.divisors := by
    intro d hd e he h
    have hfirst := congrArg Prod.fst h
    have hflag := congrArg Prod.snd h
    dsimp [f] at hfirst hflag
    have hdq := (Nat.mem_divisors.mp hd).1
    have heq := (Nat.mem_divisors.mp he).1
    have hd0 := Nat.pos_of_dvd_of_pos hdq hq
    have he0 := Nat.pos_of_dvd_of_pos heq hq
    have hprodD := Nat.div_mul_cancel hdq
    have hprodE := Nat.div_mul_cancel heq
    have hquotD := Nat.div_pos (Nat.le_of_dvd hq hdq) hd0
    by_cases hdU : d≤U <;> by_cases heU : e≤U
    · simpa [hdU,heU] using hfirst
    · simp [hdU,heU] at hflag
    · simp [hdU,heU] at hflag
    · simp only [if_neg hdU,if_neg heU] at hfirst
      nlinarith
  calc
    tau q=(q.divisors.image f).card := by rw [card_image_of_injOn hinj]; rfl
    _ ≤ (s.product (univ:Finset Bool)).card := card_le_card (by
      intro z hz
      obtain ⟨d,hd,rfl⟩ := mem_image.mp hz
      exact hmap d hd)
    _ = 2*s.card := by simp; ring

lemma tau_linear_block (c U : ℕ) (hc : 2≤c) (hU : 2*c≤U) :
    (∑ u∈Ioc U (2*U),(tau (linearQ c u):ℝ))≤2*(U:ℝ)*(H U+1) := by
  have hUp : 0<U := by omega
  have hsmall : (∑ u∈Ioc U (2*U),(tau (linearQ c u):ℝ))≤
      2*(∑ u∈Ioc U (2*U),(((Icc 1 U).filter (fun d => d∣linearQ c u)).card:ℝ)) := by
    rw [mul_sum]
    apply sum_le_sum
    intro u hu
    have hu0 : 0<u := hUp.trans (mem_Ioc.mp hu).1
    have hqu : linearQ c u≤U^2 := by
      have hule := (mem_Ioc.mp hu).2
      have hprod : c*u≤U^2 := by
        have h1 := Nat.mul_le_mul_left c hule
        have h2 := Nat.mul_le_mul_right U hU
        nlinarith
      exact (Nat.sub_le _ _).trans hprod
    exact_mod_cast tau_le_twice_small_divisors (linearQ c u) U (linearQ_pos hc hu0) hqu
  have hswap : (∑ u∈Ioc U (2*U),(((Icc 1 U).filter (fun d => d∣linearQ c u)).card:ℝ)) =
      ∑ d∈Icc 1 U,(((Ioc U (2*U)).filter (fun u => d∣linearQ c u)).card:ℝ) := by
    simp_rw [←sum_boole]
    rw [sum_comm]
  have hcounts : (∑ d∈Icc 1 U,(((Ioc U (2*U)).filter (fun u => d∣linearQ c u)).card:ℝ))≤
      (U:ℝ)*(H U+1) := by
    calc
      _ ≤ ∑ d∈Icc 1 U,((U:ℝ)/(d:ℝ)+1) := by
        apply sum_le_sum
        intro d hd
        simpa only [linearQ,show U+U=2*U by omega] using
          linear_hits_Ioc_le c d U U hc (mem_Icc.mp hd).1
      _ = (U:ℝ)*(H U+1) := by
        rw [sum_add_distrib]
        simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
        simp_rw [div_eq_mul_inv,←mul_sum]
        simp only [H,one_div]
        ring
  rw [hswap] at hsmall
  linarith

lemma weighted_tau_linear_block (c U : ℕ) (hc : 2≤c) (hU : 2*c≤U) :
    (∑ u∈Ioc U (2*U),(tau (linearQ c u):ℝ)/(linearQ c u:ℝ))≤
      4*(H U+1)/(c:ℝ) := by
  have hUp : 0<U := by omega
  have hden0 : (0:ℝ)<(c:ℝ)*(U:ℝ)/2 := by positivity
  have hs := tau_linear_block c U hc hU
  calc
    _ ≤ (∑ u∈Ioc U (2*U),(tau (linearQ c u):ℝ))/((c:ℝ)*(U:ℝ)/2) := by
      rw [sum_div]
      apply sum_le_sum
      intro u hu
      have hu0 : 0<u := hUp.trans (mem_Ioc.mp hu).1
      apply div_le_div_of_nonneg_left (by positivity) hden0
      have hbase : (c:ℝ)*(U:ℝ)/2≤(c:ℝ)*(u:ℝ)/2 := by
        gcongr
        exact_mod_cast (mem_Ioc.mp hu).1.le
      exact hbase.trans (linearQ_half hc hu0)
    _ ≤ (2*(U:ℝ)*(H U+1))/((c:ℝ)*(U:ℝ)/2) := by gcongr
    _ = 4*(H U+1)/(c:ℝ) := by
      have hc0 : (c:ℝ)≠0 := by positivity
      have hU0 : (U:ℝ)≠0 := by positivity
      field_simp
      ring

lemma harmonic_dyadic_le (n : ℕ) : H (2^n)≤n+1 := by
  have h := H_le (2^n)
  rw [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow] at h
  have hm := mul_le_mul_of_nonneg_left log_two_lt_one.le (by positivity : (0:ℝ)≤(n:ℝ))
  linarith

lemma weighted_tau_delayed (n c : ℕ) (hc : 2≤c) (hdelay : 2*c≤(2^n)^4) :
    (∑ u∈Ioc ((2^n)^4) ((2^n)^6),(tau (linearQ c u):ℝ)/(linearQ c u:ℝ))≤
      64*((n+1:ℕ):ℝ)^2/(c:ℝ) := by
  rw [←scale_range_dyadic n,dyadic_Ioc_sum]
  have hblocks : (∑ j∈range (2*n),∑ u∈Ioc (2^j*(2^n)^4) (2^(j+1)*(2^n)^4),
      (tau (linearQ c u):ℝ)/(linearQ c u:ℝ))≤
      ∑ _j∈range (2*n),4*(6*(n:ℝ)+2)/(c:ℝ) := by
    apply sum_le_sum
    intro j hj
    have hjlt := mem_range.mp hj
    have hU := hdelay.trans (Nat.le_mul_of_pos_left ((2^n)^4) (by positivity : 0<2^j))
    have hb := weighted_tau_linear_block c (2^j*(2^n)^4) hc hU
    have hUpow : 2^j*(2^n)^4=2^(j+4*n) := by
      rw [←pow_mul,←pow_add]
      congr 1
      omega
    have hH : H (2^j*(2^n)^4)≤6*(n:ℝ)+1 := by
      rw [hUpow]
      have h := harmonic_dyadic_le (j+4*n)
      have hjR : (j:ℝ)<2*(n:ℝ) := by exact_mod_cast hjlt
      push_cast at h
      linarith
    have hb' : (∑ u∈Ioc (2^j*(2^n)^4) (2^(j+1)*(2^n)^4),
        (tau (linearQ c u):ℝ)/(linearQ c u:ℝ))≤4*(H (2^j*(2^n)^4)+1)/(c:ℝ) := by
      simpa only [pow_succ,mul_assoc,mul_comm,mul_left_comm] using hb
    apply hb'.trans
    apply (div_le_div_iff_of_pos_right (by positivity : (0:ℝ)<(c:ℝ))).2
    nlinarith
  have hpoly : (∑ _j∈range (2*n),4*(6*(n:ℝ)+2)/(c:ℝ))≤64*((n+1:ℕ):ℝ)^2/(c:ℝ) := by
    simp only [sum_const,card_range,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one]
    rw [←mul_div_assoc]
    apply (div_le_div_iff_of_pos_right (by positivity : (0:ℝ)<(c:ℝ))).mpr
    nlinarith [show (0:ℝ)≤(n:ℝ) by positivity]
  exact hblocks.trans hpoly

/-- Removing the common linear coefficient uses coprimality proved from the hit. -/
lemma divides_index_difference (c d u v : ℕ) (hc : 2≤c) (hd : 0<d)
    (hu : 0<u) (huv : u≤v) (hdu : d∣linearQ c u) (hdv : d∣linearQ c v) : d∣v-u := by
  have hcq := coprime_of_linear_hit c d u hd (Nat.mul_pos (by omega) hu) hdu
  have hsub := Nat.dvd_sub hdv hdu
  have hident : linearQ c v-linearQ c u=c*(v-u) := by
    have hcu : 1≤c*u := by nlinarith
    have hcv : 1≤c*v := by nlinarith
    have huvC : c*u≤c*v := Nat.mul_le_mul_left c huv
    change c*v-1-(c*u-1)=c*(v-u)
    calc
      c*v-1-(c*u-1)=c*v-c*u := by omega
      _ = c*(v-u) := (Nat.mul_sub_left_distrib c v u).symm
  rw [hident] at hsub
  exact hcq.symm.dvd_of_dvd_mul_left hsub

/-- Later progression terms: j≥1, so no first-hit term is incorrectly suppressed. -/
lemma later_reciprocal_sum (c d u T : ℕ) (hc : 2≤c) (hd : 0<d) (hu : 0<u)
    (hdu : d∣linearQ c u) :
    (∑ v∈Ioc u T,if d∣linearQ c v then 1/(linearQ c v:ℝ) else 0)≤
      H T/((c:ℝ)*(d:ℝ)) := by
  classical
  let s := (Ioc u T).filter (fun v => d∣linearQ c v)
  let f : ℕ → ℕ := fun v => (v-u)/d
  have hindex : ∀ v∈s, d*f v=v-u := by
    intro v hv
    have hvu := (mem_Ioc.mp (mem_filter.mp hv).1).1
    have hdiv := divides_index_difference c d u v hc hd hu hvu.le hdu (mem_filter.mp hv).2
    exact Nat.mul_div_cancel' hdiv
  have hmap : ∀ v∈s,f v∈Icc 1 T := by
    intro v hv
    have hvI := mem_Ioc.mp (mem_filter.mp hv).1
    have hi := hindex v hv
    have hfpos : 0<f v := by
      apply Nat.pos_of_ne_zero
      intro hf
      simp [hf] at hi
      omega
    refine mem_Icc.mpr ⟨hfpos,?_⟩
    exact (Nat.div_le_self (v-u) d).trans ((Nat.sub_le v u).trans hvI.2)
  have hinj : Set.InjOn f s := by
    intro v hv z hz heq
    have hv' : v∈s := hv
    have hz' : z∈s := hz
    have hvI := mem_Ioc.mp (mem_filter.mp hv').1
    have hzI := mem_Ioc.mp (mem_filter.mp hz').1
    have hvq := hindex v hv'
    have hzq := hindex z hz'
    rw [heq] at hvq
    omega
  have hterm : ∀ v∈s,1/(linearQ c v:ℝ)≤1/((c:ℝ)*(d:ℝ)*(f v:ℝ)) := by
    intro v hv
    have hvI := mem_Ioc.mp (mem_filter.mp hv).1
    have hj := (mem_Icc.mp (hmap v hv)).1
    have hid : linearQ c v=linearQ c u+c*d*f v := by
      have hi := hindex v hv
      have hvu : u≤v := hvI.1.le
      have hcu : 1≤c*u := by nlinarith
      have hcv : 1≤c*v := by nlinarith
      have hvexpr : u+d*f v=v := by omega
      change c*v-1=(c*u-1)+c*d*f v
      calc
        c*v-1 = c*(u+d*f v)-1 := by rw [hvexpr]
        _ = (c*u+c*(d*f v))-1 := by rw [Nat.mul_add]
        _ = (c*u-1)+c*(d*f v) := Nat.sub_add_comm hcu
        _ = (c*u-1)+c*d*f v := by ring
    apply one_div_le_one_div_of_le (by positivity)
    rw [hid]
    push_cast
    exact le_add_of_nonneg_left (Nat.cast_nonneg (linearQ c u))
  rw [←sum_filter]
  calc
    (∑ v∈s,1/(linearQ c v:ℝ))≤∑ v∈s,1/((c:ℝ)*(d:ℝ)*(f v:ℝ)) := sum_le_sum hterm
    _ ≤ ∑ j∈Icc 1 T,1/((c:ℝ)*(d:ℝ)*(j:ℝ)) :=
      sum_le_sum_of_injOn s (Icc 1 T) f (fun j => 1/((c:ℝ)*(d:ℝ)*(j:ℝ)))
        hmap hinj (fun j hj => by positivity)
    _ = H T/((c:ℝ)*(d:ℝ)) := by
      rw [H,sum_div]
      apply sum_congr rfl
      intro j hj
      ring

/-- Exact expansion of the full gcd into common divisors. -/
lemma gcd_totient_expansion (q r : ℕ) (hq : 0<q) :
    (Nat.gcd q r:ℝ)=∑ d∈q.divisors,if d∣r then (Nat.totient d:ℝ) else 0 := by
  have hg : 0<Nat.gcd q r := Nat.gcd_pos_of_pos_left r hq
  have hset : (Nat.gcd q r).divisors=q.divisors.filter (fun d => d∣r) := by
    ext d
    simp only [Nat.mem_divisors, mem_filter, Nat.dvd_gcd_iff, hq.ne', hg.ne', and_true]
    aesop
  calc
    (Nat.gcd q r:ℝ) = ((Nat.gcd q r).divisors.sum Nat.totient:ℕ) := by
      exact_mod_cast (Nat.sum_totient (Nat.gcd q r)).symm
    _ = ∑ d∈q.divisors,if d∣r then (Nat.totient d:ℝ) else 0 := by
      rw [Nat.cast_sum, hset, sum_filter]

lemma gcdKernel_le_weighted_tau (c L T : ℕ) (hc : 2≤c) :
    gcdKernel c L T≤H T/(c:ℝ)*
      (∑ u∈Ioc L T,(tau (linearQ c u):ℝ)/(linearQ c u:ℝ)) := by
  classical
  unfold gcdKernel
  rw [mul_sum]
  apply sum_le_sum
  intro u hu
  have hu0 : 0<u := lt_of_le_of_lt (Nat.zero_le L) (mem_Ioc.mp hu).1
  have hq0 := linearQ_pos hc hu0
  have hqR : (0:ℝ)<(linearQ c u:ℝ) := by exact_mod_cast hq0
  have heq : (∑ v∈Ioc u T,(Nat.gcd (linearQ c u) (linearQ c v):ℝ)/
      ((linearQ c u:ℝ)*(linearQ c v:ℝ))) =
      ∑ d∈(linearQ c u).divisors,(Nat.totient d:ℝ)/(linearQ c u:ℝ)*
        (∑ v∈Ioc u T,if d∣linearQ c v then 1/(linearQ c v:ℝ) else 0) := by
    simp_rw [gcd_totient_expansion _ _ hq0,sum_div]
    rw [sum_comm]
    apply sum_congr rfl
    intro d hd
    rw [mul_sum]
    apply sum_congr rfl
    intro v hv
    split_ifs <;> ring
  rw [heq]
  calc
    _ ≤ ∑ d∈(linearQ c u).divisors,(Nat.totient d:ℝ)/(linearQ c u:ℝ)*
        (H T/((c:ℝ)*(d:ℝ))) := by
      apply sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left
        (later_reciprocal_sum c d u T hc (Nat.pos_of_mem_divisors hd) hu0
          (Nat.mem_divisors.mp hd).1) (by positivity)
    _ ≤ ∑ _d∈(linearQ c u).divisors,H T/((c:ℝ)*(linearQ c u:ℝ)) := by
      apply sum_le_sum
      intro d hd
      have hd0 : (0:ℝ)<(d:ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd
      have ht : (Nat.totient d:ℝ)≤(d:ℝ) := by exact_mod_cast Nat.totient_le d
      calc
        _ = (Nat.totient d:ℝ)/(d:ℝ)*(H T/((c:ℝ)*(linearQ c u:ℝ))) := by ring
        _ ≤ 1*(H T/((c:ℝ)*(linearQ c u:ℝ))) := by
          exact mul_le_mul_of_nonneg_right ((div_le_one hd0).mpr ht) (by (have := H_nonneg T; positivity))
        _ = _ := one_mul _
    _ = H T/(c:ℝ)*((tau (linearQ c u):ℝ)/(linearQ c u:ℝ)) := by
      simp only [sum_const,nsmul_eq_mul,tau]
      ring

/-- The weaker logarithmic kernel is sufficient for the original preprint conclusion. -/
theorem gcdKernel_delayed (n c : ℕ) (hc : 2≤c) (hdelay : 2*c≤(2^n)^4) :
    gcdKernel c ((2^n)^4) ((2^n)^6)≤384*((n+1:ℕ):ℝ)^3/(c:ℝ)^2 := by
  have h := gcdKernel_le_weighted_tau c ((2^n)^4) ((2^n)^6) hc
  have ht := weighted_tau_delayed n c hc hdelay
  have hH : H ((2^n)^6)≤6*((n+1:ℕ):ℝ) := by
    rw [←pow_mul]
    have hh := harmonic_dyadic_le (n*6)
    push_cast at hh ⊢
    linarith
  calc
    _ ≤ H ((2^n)^6)/(c:ℝ)*(∑ u∈Ioc ((2^n)^4) ((2^n)^6),
        (tau (linearQ c u):ℝ)/(linearQ c u:ℝ)) := h
    _ ≤ (6*((n+1:ℕ):ℝ)/(c:ℝ))*(64*((n+1:ℕ):ℝ)^2/(c:ℝ)) := by
      apply mul_le_mul
      · exact div_le_div_of_nonneg_right hH (by positivity)
      · exact ht
      · exact sum_nonneg (fun u _ => by positivity)
      · positivity
    _ = 384*((n+1:ℕ):ℝ)^3/(c:ℝ)^2 := by ring

end
end PrimeAbundance.Analytic
