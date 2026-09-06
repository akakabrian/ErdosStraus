/- Finite transfer proved for the selected family itself.
No substituted full-family variance, no prime equidistribution, no lcm endpoint loss. -/
import PrimeAbundance.Decoder
import PrimeAbundance.AnalyticBounds

set_option autoImplicit false
open scoped Classical
open scoped BigOperators
open Finset

namespace PrimeAbundance
noncomputable section
open Analytic

namespace Late

def fireIndicator (p : Packet) (n : ℕ) : ℝ := indicator (Q p ∣ n+4*p.2)
def overlapWeight (p q : Packet) : ℝ :=
  if Q p < Q q ∧ 1 < Nat.gcd (Q p) (Q q) ∧ Nat.ModEq (Nat.gcd (Q p) (Q q)) p.2 q.2
  then (Nat.gcd (Q p) (Q q):ℝ)/((Q p:ℝ)*(Q q:ℝ)) else 0

lemma fireIndicator_nonneg (p : Packet) (n : ℕ) : 0 ≤ fireIndicator p n := indicator_nonneg _
lemma overlapWeight_nonneg (p q : Packet) : 0 ≤ overlapWeight p q := by
  unfold overlapWeight
  split_ifs <;> positivity

lemma firingCount_eq_sum (B n : ℕ) :
    (firingCount B n:ℝ)=∑ p∈packets B,fireIndicator p n := by
  simp only [firingCount,fireIndicator,indicator,sum_boole]

lemma firing_residue (q s n : ℕ) :
    q∣n+4*s ↔ (n:ZMod q)=-(4*(s:ZMod q)) := by
  rw [←ZMod.natCast_eq_zero_iff]
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  exact add_eq_zero_iff_eq_neg

lemma indicator_product (P R : Prop) [Decidable P] [Decidable R] :
    indicator P*indicator R=indicator (P∧R) := by
  by_cases hP:P <;> by_cases hR:R <;> simp [indicator,hP,hR]

lemma fireIndicator_error (p : Packet) (A H : ℕ) (hq : 0 < Q p) :
    |(∑ i:Fin H,fireIndicator p (A+i.val))-(H:ℝ)/(Q p:ℝ)|≤1 := by
  simp only [fireIndicator,firing_residue]
  exact residue_indicator_error (Q p) A H hq (-(4*(p.2:ZMod (Q p))))

lemma natCast_modEq (q a b : ℕ) (hq : 0 < q) (h : (a:ZMod q)=(b:ZMod q)) : Nat.ModEq q a b := by
  letI : NeZero q := ⟨hq.ne'⟩
  have hv := congrArg (ZMod.val : ZMod q→ℕ) h
  simpa only [ZMod.val_natCast] using hv

/-- Simultaneous firings force compatibility at the full gcd. -/
lemma fires_compatible {Y n : ℕ} {p q : Packet} (hp : Authentic Y p) (hq : Authentic Y q)
    (hfp : Q p ∣ n+4*p.2) (hfq : Q q ∣ n+4*q.2) :
    Nat.ModEq (Nat.gcd (Q p) (Q q)) p.2 q.2 := by
  let g := Nat.gcd (Q p) (Q q)
  have hg : 0 < g := Nat.gcd_pos_of_pos_left (Q q) (authentic_Q_pos hp)
  letI : NeZero g := ⟨hg.ne'⟩
  have hgp : g ∣ Q p := Nat.gcd_dvd_left _ _
  have hcp : Nat.Coprime 4 g := by
    apply coprime_of_linear_hit 4 g p.1 hg
    · have hp1 : 0 < p.1 := lt_of_lt_of_le Nat.zero_lt_one hp.1
      exact hp.1.trans (Nat.le_mul_of_pos_left p.1 (by decide : 0 < 4))
    · have hQ := authentic_Q_add_one hp
      convert hgp using 1 <;> omega
  have hunit : IsUnit (4:ZMod g) := by
    exact (ZMod.isUnit_iff_coprime 4 g).mpr hcp
  have h1 : (n:ZMod g)+4*(p.2:ZMod g)=0 := by
    have h := (ZMod.natCast_eq_zero_iff _ g).mpr (hgp.trans hfp)
    simpa using h
  have h2 : (n:ZMod g)+4*(q.2:ZMod g)=0 := by
    have h := (ZMod.natCast_eq_zero_iff _ g).mpr ((Nat.gcd_dvd_right (Q p) (Q q)).trans hfq)
    simpa using h
  have hprod : (4:ZMod g)*(p.2:ZMod g)=4*(q.2:ZMod g) :=
    add_left_cancel (h1.trans h2.symm)
  have hval : (p.2:ZMod g)=(q.2:ZMod g) := by
    exact hunit.mul_left_cancel hprod
  exact natCast_modEq g p.2 q.2 hg hval

lemma same_row_no_double {Y n : ℕ} {p q : Packet} (hp : Authentic Y p) (hq : Authentic Y q)
    (hQ : Q p = Q q) (hpq : p ≠ q) : ¬(Q p ∣ n+4*p.2 ∧ Q q ∣ n+4*q.2) := by
  rintro ⟨hfp,hfq⟩
  have hcomp := fires_compatible hp hq hfp hfq
  have hM : p.1=q.1 := by
    have h1 := authentic_Q_add_one hp
    have h2 := authentic_Q_add_one hq
    omega
  have hps : p.2 < Q p := by
    have h1 := authentic_Q_add_one hp
    have hM0 := hp.1
    have hs := hp.2.2.2.2.1
    omega
  have hqs : q.2 < Q q := by
    have h1 := authentic_Q_add_one hq
    have hM0 := hq.1
    have hs := hq.2.2.2.2.1
    omega
  have hrem : p.2%Q p=q.2%Q p := by simpa [hQ] using hcomp
  rw [Nat.mod_eq_of_lt hps,Nat.mod_eq_of_lt (by simpa [hQ] using hqs)] at hrem
  exact hpq (Prod.ext hM hrem)

/-- Two congruent offsets differ by a multiple of the modulus. -/
lemma offset_difference_dvd (q c i j : ℕ) (hji : j ≤ i)
    (hi : q ∣ i+c) (hj : q ∣ j+c) : q ∣ i-j := by
  have h := Nat.dvd_sub hi hj
  simpa only [Nat.add_sub_add_right] using h

/-- Pair upper count needs only lcm divisibility, not CRT existence. -/
lemma pair_count_upper (p q : Packet) (A H : ℕ) (hp : 0 < Q p) (hq : 0 < Q q) :
    (∑ i:Fin H,fireIndicator p (A+i.val)*fireIndicator q (A+i.val))≤
      (H:ℝ)/(Nat.lcm (Q p) (Q q):ℝ)+1 := by
  classical
  let L := Nat.lcm (Q p) (Q q)
  have hL : 0 < L := Nat.lcm_pos hp hq
  letI : NeZero L := ⟨hL.ne'⟩
  let F : Finset (Fin H) := univ.filter (fun i =>
    Q p∣A+i.val+4*p.2 ∧ Q q∣A+i.val+4*q.2)
  have hcount : (∑ i:Fin H,fireIndicator p (A+i.val)*fireIndicator q (A+i.val))=(F.card:ℝ) := by
    simp only [fireIndicator, indicator_product]
    simpa only [F] using
      (sum_boole (fun i : Fin H =>
        Q p ∣ A+i.val+4*p.2 ∧ Q q ∣ A+i.val+4*q.2) univ)
  rw [hcount]
  by_cases hF : F.Nonempty
  · obtain ⟨j,hj⟩ := hF
    have hfiresJ := (mem_filter.mp hj).2
    have hsame : ∀ i∈F,(i.val:ZMod L)=(j.val:ZMod L) := by
      intro i hi
      have hfiresI := (mem_filter.mp hi).2
      have hcase : ∀ a b:Fin H,
          (Q p∣A+a.val+4*p.2 ∧ Q q∣A+a.val+4*q.2) →
          (Q p∣A+b.val+4*p.2 ∧ Q q∣A+b.val+4*q.2) → b.val≤a.val →
          (a.val:ZMod L)=(b.val:ZMod L) := by
        intro a b ha hb hab
        have h1 : Q p∣a.val-b.val := offset_difference_dvd (Q p) (A+4*p.2) _ _ hab
          (by simpa [add_assoc,add_comm,add_left_comm] using ha.1)
          (by simpa [add_assoc,add_comm,add_left_comm] using hb.1)
        have h2 : Q q∣a.val-b.val := offset_difference_dvd (Q q) (A+4*q.2) _ _ hab
          (by simpa [add_assoc,add_comm,add_left_comm] using ha.2)
          (by simpa [add_assoc,add_comm,add_left_comm] using hb.2)
        have hd : L∣a.val-b.val := Nat.lcm_dvd h1 h2
        have hz := (ZMod.natCast_eq_zero_iff _ L).mpr hd
        simpa only [Nat.cast_sub hab,sub_eq_zero] using hz
      rcases le_total j.val i.val with h|h
      · exact hcase i j hfiresI hfiresJ h
      · exact (hcase j i hfiresJ hfiresI h).symm
    let f : F → ResidueHits L 0 H (j.val:ZMod L) := fun i =>
      ⟨i.val,by simpa using hsame i.val i.property⟩
    have hinj : Function.Injective f := by
      intro i k h
      have hv := congrArg (fun z : ResidueHits L 0 H (j.val:ZMod L) => z.val.val) h
      dsimp [f] at hv
      apply Subtype.ext
      exact Fin.ext hv
    have hc : F.card ≤ Nat.card (ResidueHits L 0 H (j.val:ZMod L)) := by
      simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using Fintype.card_le_of_injective f hinj
    have he := residueHits_error L 0 H hL (j.val:ZMod L)
    have hu := (abs_le.mp he).2
    have hcR : (F.card:ℝ)≤(Nat.card (ResidueHits L 0 H (j.val:ZMod L)):ℝ) := by exact_mod_cast hc
    linarith
  · have h0 : F=∅ := not_nonempty_iff_eq_empty.mp hF
    rw [h0]
    simp only [card_empty,Nat.cast_zero]
    positivity

lemma inverse_lcm (q r : ℕ) (hq : 0 < q) (hr : 0 < r) :
    1/(Nat.lcm q r:ℝ)=(Nat.gcd q r:ℝ)/((q:ℝ)*(r:ℝ)) := by
  have hl : (0:ℝ)<(Nat.lcm q r:ℝ) := by exact_mod_cast Nat.lcm_pos hq hr
  have hqR : (0:ℝ)<(q:ℝ) := by exact_mod_cast hq
  have hrR : (0:ℝ)<(r:ℝ) := by exact_mod_cast hr
  apply (div_eq_div_iff hl.ne' (mul_pos hqR hrR).ne').mpr
  simpa only [one_mul,Nat.cast_mul] using congrArg (fun n:ℕ => (n:ℝ)) (Nat.gcd_mul_lcm q r).symm

/-- Pointwise pair budget. The diagonal is counted once, while ordered pairs carry both orientations. -/
lemma pair_second_moment_bound {Y : ℕ} (p q : Packet) (hp : Authentic Y p) (hq : Authentic Y q)
    (A H : ℕ) :
    (∑ i:Fin H,fireIndicator p (A+i.val)*fireIndicator q (A+i.val))≤
      (H:ℝ)*(1/(Q p:ℝ)* (1/(Q q:ℝ))+
        (if p=q then 1/(Q p:ℝ) else 0)+overlapWeight p q+overlapWeight q p)+1 := by
  classical
  have hp0 := authentic_Q_pos hp
  have hq0 := authentic_Q_pos hq
  by_cases hpq : p=q
  · subst q
    have he : (∑ i:Fin H,fireIndicator p (A+i.val)*fireIndicator p (A+i.val))=
        ∑ i:Fin H,fireIndicator p (A+i.val) := by
      apply sum_congr rfl
      intro i hi
      dsimp [fireIndicator,indicator]
      split_ifs <;> norm_num
    rw [he]
    have hu := (abs_le.mp (fireIndicator_error p A H hp0)).2
    simp only [if_true,overlapWeight,lt_self_iff_false,false_and,if_false,add_zero]
    have hnn : (0:ℝ) ≤ (H:ℝ)*(1/(Q p:ℝ))^2 := by positivity
    calc
      _ ≤ (H:ℝ)/(Q p:ℝ)+1 := by linarith
      _ ≤ (H:ℝ)*(1/(Q p:ℝ)*(1/(Q p:ℝ))+1/(Q p:ℝ))+1 := by
        rw [mul_add]
        have heq : (H:ℝ)/(Q p:ℝ) = (H:ℝ)*(1/(Q p:ℝ)) := by ring
        rw [heq]
        have hstep : (H:ℝ)*(1/(Q p:ℝ)) ≤
            (H:ℝ)*(1/(Q p:ℝ)*(1/(Q p:ℝ)))+(H:ℝ)*(1/(Q p:ℝ)) :=
          le_add_of_nonneg_left (by simpa [pow_two] using hnn)
        simpa only [add_comm, add_left_comm, add_assoc] using add_le_add_right hstep 1
  by_cases hQ : Q p=Q q
  · have he : (∑ i:Fin H,fireIndicator p (A+i.val)*fireIndicator q (A+i.val))=0 := by
      apply sum_eq_zero
      intro i hi
      rw [fireIndicator,fireIndicator,indicator_product]
      simp [indicator,same_row_no_double hp hq hQ hpq]
    rw [he]
    exact add_nonneg (mul_nonneg (by positivity) (by
      simp only [if_neg hpq]
      exact add_nonneg (add_nonneg (add_nonneg (by positivity) (by norm_num))
        (overlapWeight_nonneg p q)) (overlapWeight_nonneg q p))) (by norm_num)
  let g := Nat.gcd (Q p) (Q q)
  have hg0 : 0<g := Nat.gcd_pos_of_pos_left _ hp0
  by_cases hcompat : Nat.ModEq g p.2 q.2
  · have hup := pair_count_upper p q A H hp0 hq0
    have hinv := inverse_lcm (Q p) (Q q) hp0 hq0
    have heq : (H:ℝ)/(Nat.lcm (Q p) (Q q):ℝ)=
        (H:ℝ)*(g:ℝ)/((Q p:ℝ)*(Q q:ℝ)) := by
      calc
        _ = (H:ℝ)*(1/(Nat.lcm (Q p) (Q q):ℝ)) := by ring
        _ = _ := by rw [hinv]; dsimp [g]; ring
    rw [heq] at hup
    by_cases hg1 : g=1
    · have hww : overlapWeight p q=0 ∧ overlapWeight q p=0 := by
        simp [overlapWeight,g,hg1,Nat.gcd_comm]
      rw [if_neg hpq,hww.1,hww.2]
      rw [hg1] at hup
      calc
        _ ≤ (H:ℝ)/((Q p:ℝ)*(Q q:ℝ))+1 := by simpa only [Nat.cast_one, mul_one] using hup
        _ = (H:ℝ)*(1/(Q p:ℝ)*(1/(Q q:ℝ)))+1 := by ring
        _ ≤ (H:ℝ)*(1/(Q p:ℝ)*(1/(Q q:ℝ))+0+0+0)+1 := by
          ring_nf
          exact le_rfl
    · have hg : 1<g := by omega
      have hsum : overlapWeight p q+overlapWeight q p=(g:ℝ)/((Q p:ℝ)*(Q q:ℝ)) := by
        rcases lt_or_gt_of_ne hQ with hlt|hgt
        · simp [overlapWeight,hlt,hlt.not_gt,hg,hcompat,g,Nat.gcd_comm,hcompat.symm,
            mul_comm]
        · simp [overlapWeight,hgt,hgt.not_gt,hg,hcompat,g,Nat.gcd_comm,hcompat.symm,
            mul_comm]
      rw [if_neg hpq,add_zero,add_assoc _ (overlapWeight p q) (overlapWeight q p),hsum]
      have hnn : (0:ℝ)≤(H:ℝ)*(1/(Q p:ℝ)* (1/(Q q:ℝ))) := by positivity
      calc
        _ ≤ (H:ℝ)*(g:ℝ)/((Q p:ℝ)*(Q q:ℝ))+1 := hup
        _ ≤ (H:ℝ)*(1/(Q p:ℝ)*(1/(Q q:ℝ))+
            (g:ℝ)/((Q p:ℝ)*(Q q:ℝ)))+1 := by
          rw [mul_add]
          have hstep : (H:ℝ)*(g:ℝ)/((Q p:ℝ)*(Q q:ℝ)) ≤
              (H:ℝ)*(1/(Q p:ℝ)*(1/(Q q:ℝ)))+
                (H:ℝ)*(g:ℝ)/((Q p:ℝ)*(Q q:ℝ)) :=
            le_add_of_nonneg_left hnn
          convert add_le_add_right hstep 1 using 1 <;> ring
  · have he : (∑ i:Fin H,fireIndicator p (A+i.val)*fireIndicator q (A+i.val))=0 := by
      apply sum_eq_zero
      intro i hi
      rw [fireIndicator,fireIndicator,indicator_product]
      have hnot : ¬(Q p∣A+i.val+4*p.2 ∧ Q q∣A+i.val+4*q.2) := by
        rintro ⟨h1,h2⟩
        exact hcompat (fires_compatible hp hq h1 h2)
      simp [indicator,hnot]
    rw [he]
    have hnn : (0:ℝ)≤1/(Q p:ℝ)* (1/(Q q:ℝ))+
        (if p=q then 1/(Q p:ℝ) else 0)+overlapWeight p q+overlapWeight q p := by
      rw [if_neg hpq]
      exact add_nonneg (add_nonneg (add_nonneg (by positivity) (by norm_num))
        (overlapWeight_nonneg p q)) (overlapWeight_nonneg q p)
    positivity

lemma first_moment_lower (B A H : ℕ) :
    (H:ℝ)*mean B-((packets B).card:ℝ)≤
      ∑ i:Fin H,(firingCount B (A+i.val):ℝ) := by
  simp_rw [firingCount_eq_sum]
  rw [sum_comm]
  have h : (∑ p∈packets B,((H:ℝ)/(Q p:ℝ)-1))≤
      ∑ p∈packets B,∑ i:Fin H,fireIndicator p (A+i.val) := by
    apply sum_le_sum
    intro p hp
    have he := fireIndicator_error p A H (authentic_Q_pos (mem_packets_authentic B p hp))
    linarith [(abs_le.mp he).1]
  simpa only [sum_sub_distrib,sum_const,nsmul_eq_mul,mul_one,mean,mul_sum,mul_one_div] using h

lemma second_moment_upper (B A H : ℕ) :
    (∑ i:Fin H,(firingCount B (A+i.val):ℝ)^2)≤
      (H:ℝ)*((mean B)^2+mean B+2*overlap B)+((packets B).card:ℝ)^2 := by
  classical
  have hexpand : (∑ i:Fin H,(firingCount B (A+i.val):ℝ)^2)=
      ∑ p∈packets B,∑ q∈packets B,∑ i:Fin H,
        fireIndicator p (A+i.val)*fireIndicator q (A+i.val) := by
    simp_rw [firingCount_eq_sum,pow_two,sum_mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro p hp
    rw [sum_comm]
  rw [hexpand]
  have h := sum_le_sum (fun p hp => sum_le_sum (fun q hq =>
    pair_second_moment_bound p q (mem_packets_authentic B p hp) (mem_packets_authentic B q hq) A H))
  apply h.trans
  apply le_of_eq
  have hbase : (∑ p∈packets B,∑ q∈packets B,1/(Q p:ℝ)*(1/(Q q:ℝ)))=(mean B)^2 := by
    simp_rw [←mul_sum,←sum_mul]
    simp only [mean,pow_two]
  have hdiag : (∑ p∈packets B,∑ q∈packets B,if p=q then 1/(Q p:ℝ) else 0)=mean B := by
    apply sum_congr rfl
    intro p hp
    simp [hp]
  have hforward : (∑ p∈packets B,∑ q∈packets B,overlapWeight p q)=overlap B := rfl
  have hbackward : (∑ p∈packets B,∑ q∈packets B,overlapWeight q p)=overlap B := by
    rw [sum_comm]
    rfl
  -- Expand the budget pointwise before collecting its four finite sums.
  -- Unrestricted reverse `mul_sum` rewrites can consume the base sum that
  -- `hbase` is supposed to rewrite, or leave sums of undispersed addends.
  calc
    _ = (H:ℝ)*
        ((∑ p∈packets B,∑ q∈packets B,1/(Q p:ℝ)*(1/(Q q:ℝ))) +
         (∑ p∈packets B,∑ q∈packets B,if p=q then 1/(Q p:ℝ) else 0) +
         (∑ p∈packets B,∑ q∈packets B,overlapWeight p q) +
         (∑ p∈packets B,∑ q∈packets B,overlapWeight q p)) +
        ((packets B).card:ℝ)^2 := by
      simp only [mul_add,mul_sum,sum_add_distrib,sum_const,nsmul_eq_mul,
        mul_one,pow_two] <;> ring
    _ = (H:ℝ)*((mean B)^2+mean B+2*overlap B)+
        ((packets B).card:ℝ)^2 := by
      rw [hbase,hdiag,hforward,hbackward]
      ring

lemma packet_card_over_mean (B : ℕ) (hB : 0 < B) (hμ : 0 < mean B) :
    ((packets B).card:ℝ)/mean B ≤ 12*(B:ℝ)^8 := by
  have hbound : (0:ℝ) < 12*(B:ℝ)^8 := by positivity
  have hsum : ((packets B).card:ℝ)/(12*(B:ℝ)^8) ≤ mean B := by
    calc
      _ = ∑ _p∈packets B,1/(12*(B:ℝ)^8) := by simp; ring
      _ ≤ mean B := by
        apply sum_le_sum
        intro p hp
        have hpa := mem_packets_authentic B p hp
        have hq0 : (0:ℝ) < (Q p:ℝ) := by exact_mod_cast authentic_Q_pos hpa
        exact one_div_le_one_div_of_le hq0 (by exact_mod_cast (authentic_Q_lt hpa).le)
  have hmul := (div_le_iff₀ hbound).mp hsum
  apply (div_le_iff₀ hμ).mpr
  nlinarith

lemma normalized_square_bound (B A H : ℕ) (hB : 0 < B) (hμ : 0 < mean B) :
    (∑ i:Fin H,(1-(firingCount B (A+i.val):ℝ)/mean B)^2)≤
      (H:ℝ)*(mean B+2*overlap B)/(mean B)^2+(1+12*(B:ℝ)^8)^2 := by
  let μ := mean B
  let m : ℝ := ((packets B).card:ℝ)
  let S₁ : ℝ := ∑ i:Fin H,(firingCount B (A+i.val):ℝ)
  let S₂ : ℝ := ∑ i:Fin H,(firingCount B (A+i.val):ℝ)^2
  have hμpos : 0 < μ := by simpa [μ] using hμ
  have hμ0 : μ ≠ 0 := hμpos.ne'
  have hfirst : (H:ℝ)*μ-m≤S₁ := first_moment_lower B A H
  have hsecond : S₂≤(H:ℝ)*(μ^2+μ+2*overlap B)+m^2 := second_moment_upper B A H
  have hexpand : (∑ i:Fin H,(1-(firingCount B (A+i.val):ℝ)/μ)^2)=
      (H:ℝ)-2*S₁/μ+S₂/μ^2 := by
    have hpoint : ∀ t:ℝ,(1-t/μ)^2=1-2*t/μ+t^2/μ^2 := by intro t; ring
    simp_rw [hpoint]
    dsimp only [S₁, S₂]
    simp only [sum_add_distrib, sum_sub_distrib, sum_div, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [←sum_div, ←mul_sum]
  rw [hexpand]
  have hlinear : -2*S₁/μ≤-2*((H:ℝ)*μ-m)/μ := by
    exact div_le_div_of_nonneg_right (by linarith) hμpos.le
  have hquadratic := div_le_div_of_nonneg_right hsecond (sq_nonneg μ)
  have hident : (H:ℝ)-2*((H:ℝ)*μ-m)/μ+
      ((H:ℝ)*(μ^2+μ+2*overlap B)+m^2)/μ^2=
      (H:ℝ)*(μ+2*overlap B)/μ^2+2*m/μ+(m/μ)^2 := by
    field_simp
    ring
  have hraw : (H:ℝ)-2*S₁/μ+S₂/μ^2≤
      (H:ℝ)*(μ+2*overlap B)/μ^2+2*m/μ+(m/μ)^2 := by
    rw [←hident]
    have hlinear' : -(2*S₁/μ) ≤ -(2*((H:ℝ)*μ-m)/μ) := by
      convert hlinear using 1 <;> ring
    exact add_le_add (add_le_add le_rfl hlinear') hquadratic
  have hm0 : 0 ≤ m/μ := by positivity
  have hmr := packet_card_over_mean B hB hμ
  change m/μ≤12*(B:ℝ)^8 at hmr
  have hsquare := pow_le_pow_left₀ (by positivity : (0:ℝ)≤1+m/μ)
    (show 1+m/μ≤1+12*(B:ℝ)^8 by linarith) 2
  calc
    _ ≤ (H:ℝ)*(μ+2*overlap B)/μ^2+2*m/μ+(m/μ)^2 := hraw
    _ ≤ (H:ℝ)*(μ+2*overlap B)/μ^2+(1+12*(B:ℝ)^8)^2 := by
      have htail0 : 2*m/μ+(m/μ)^2 ≤ (1+m/μ)^2 := by
        ring_nf
        norm_num
      have htail : 2*m/μ+(m/μ)^2 ≤ (1+12*(B:ℝ)^8)^2 := htail0.trans hsquare
      convert add_le_add_left htail ((H:ℝ)*(μ+2*overlap B)/μ^2) using 1 <;> ring
    _ = _ := by rfl

def lowerTail (B A H : ℕ) : Finset (Fin H) :=
  univ.filter (fun i => (firingCount B (A+i.val):ℝ) ≤ mean B/2)

def badOffsets (A H r : ℕ) : Finset (Fin H) :=
  univ.filter (fun i => Nat.Prime (A+i.val) ∧ ¬HasAtLeastTypeIISolutions (A+i.val) r)

lemma lowerTail_bound (B A H : ℕ) (hB : 0 < B) (hμ : 0 < mean B) :
    ((lowerTail B A H).card:ℝ)≤
      4*((H:ℝ)*(mean B+2*overlap B)/(mean B)^2+(1+12*(B:ℝ)^8)^2) := by
  have hpoint : ∀ i∈lowerTail B A H,(1:ℝ)≤4*(1-(firingCount B (A+i.val):ℝ)/mean B)^2 := by
    intro i hi
    have hlow : (firingCount B (A+i.val):ℝ) ≤ mean B/2 := by
      simpa only [lowerTail, mem_filter, mem_univ, true_and] using hi
    have hdiv : (firingCount B (A+i.val):ℝ)/mean B≤1/2 := by
      apply (div_le_iff₀ hμ).mpr
      nlinarith
    nlinarith [sq_nonneg (1/2-(firingCount B (A+i.val):ℝ)/mean B)]
  calc
    ((lowerTail B A H).card:ℝ)=∑ _i∈lowerTail B A H,(1:ℝ) := by simp
    _ ≤ ∑ i∈lowerTail B A H,4*(1-(firingCount B (A+i.val):ℝ)/mean B)^2 := sum_le_sum hpoint
    _ ≤ ∑ i:Fin H,4*(1-(firingCount B (A+i.val):ℝ)/mean B)^2 :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _ => by positivity)
    _ = 4*(∑ i:Fin H,(1-(firingCount B (A+i.val):ℝ)/mean B)^2) := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (normalized_square_bound B A H hB hμ) (by norm_num)

/-- Literal finite exceptional bound for the restricted packets. -/
theorem finite_exceptional_bound (B A H r : ℕ) (hB : 0 < B) (hμ : 0 < mean B)
    (hA : 12*B^8 < A) (hr : (r:ℝ) ≤ mean B/2) :
    ((badOffsets A H r).card:ℝ)≤
      4*((H:ℝ)*(mean B+2*overlap B)/(mean B)^2+(1+12*(B:ℝ)^8)^2) := by
  have hsub : badOffsets A H r⊆lowerTail B A H := by
    intro i hi
    obtain ⟨hprime,hbad⟩ := (mem_filter.mp hi).2
    simp only [lowerTail, mem_filter, mem_univ, true_and]
    by_contra h
    have hlarge : 12*B^8<A+i.val := hA.trans_le (Nat.le_add_right A i.val)
    have hnat : r≤firingCount B (A+i.val) := by
      exact_mod_cast (hr.trans (le_of_not_ge h))
    exact hbad (hasAtLeast_of_firingCount B (A+i.val) r hprime hlarge hnat)
  have hcard : ((badOffsets A H r).card:ℝ)≤((lowerTail B A H).card:ℝ) := by
    exact_mod_cast card_le_card hsub
  exact hcard.trans (lowerTail_bound B A H hB hμ)

end Late
end
end PrimeAbundance
