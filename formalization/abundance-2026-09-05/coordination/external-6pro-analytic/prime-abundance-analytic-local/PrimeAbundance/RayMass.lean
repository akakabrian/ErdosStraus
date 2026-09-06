/- Harmonic mass of primitive rays. All bounds are finite before the growth step. -/
import PrimeAbundance.PrimeProduct

set_option autoImplicit false
open scoped Classical
open scoped BigOperators
open Finset

namespace PrimeAbundance.Analytic
noncomputable section

abbrev NatPair := ℕ × ℕ

def pairWeight (p : NatPair) : ℝ := 1/((p.1:ℝ)*(p.2:ℝ))
def pairBox (B : ℕ) : Finset NatPair := (Icc 1 B).product (Icc 1 B)
def coprimeBox (B : ℕ) : Finset NatPair := (pairBox B).filter (fun p => Nat.Coprime p.1 p.2)
def raySet (K B : ℕ) : Finset NatPair :=
  (coprimeBox B).filter (fun p => K≤p.1 ∧ p.1<p.2)
def rayMass (K B : ℕ) : ℝ := ∑ p∈raySet K B, pairWeight p

def coprimeMass (B : ℕ) : ℝ := ∑ p∈coprimeBox B, pairWeight p

lemma pairWeight_nonneg (p : NatPair) : 0≤pairWeight p := by unfold pairWeight; positivity

lemma mem_pairBox {B a b : ℕ} : (a,b)∈pairBox B ↔ 1≤a ∧ a≤B ∧ 1≤b ∧ b≤B := by
  simp [pairBox, and_assoc]

lemma pairBox_weight (B : ℕ) : (∑ p∈pairBox B, pairWeight p) = (H B)^2 := by
  rw [pairBox, Finset.product_eq_sprod, sum_product]
  change (∑ a∈Icc 1 B, ∑ b∈Icc 1 B, 1/((a:ℝ)*(b:ℝ)))=(H B)^2
  have hterm : ∀ a b:ℕ, 1/((a:ℝ)*(b:ℝ))=(1/(a:ℝ))*(1/(b:ℝ)) := by
    intro a b
    rw [one_div_mul_one_div]
  simp_rw [hterm, ← mul_sum, ← sum_mul]
  simp only [H, pow_two]

/-- Gcd reduction maps each pair injectively to a scale and a primitive pair. -/
lemma harmonic_square_le_two_coprimeMass (B : ℕ) : (H B)^2 ≤ 2*coprimeMass B := by
  classical
  let f : NatPair → ℕ × NatPair := fun p =>
    (Nat.gcd p.1 p.2, (p.1/Nat.gcd p.1 p.2, p.2/Nat.gcd p.1 p.2))
  let target := (Icc 1 B).product (coprimeBox B)
  let wt : ℕ × NatPair → ℝ := fun t => 1/(t.1:ℝ)^2 * pairWeight t.2
  have hmap : ∀ p∈pairBox B, f p∈target := by
    rintro ⟨a,b⟩ hp
    obtain ⟨ha,haB,hb,hbB⟩ := mem_pairBox.mp hp
    have hg : 0<Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha
    have hga := Nat.gcd_dvd_left a b
    have hgb := Nat.gcd_dvd_right a b
    have hglea := Nat.le_of_dvd ha hga
    have hgleb := Nat.le_of_dvd hb hgb
    have haq : 1≤a/Nat.gcd a b := Nat.div_pos hglea hg
    have hbq : 1≤b/Nat.gcd a b := Nat.div_pos hgleb hg
    dsimp [f,target]
    apply mem_product.mpr
    refine ⟨mem_Icc.mpr ⟨hg,hglea.trans haB⟩, mem_filter.mpr ⟨?_,?_⟩⟩
    · exact mem_pairBox.mpr ⟨haq,(Nat.div_le_self _ _).trans haB,
        hbq,(Nat.div_le_self _ _).trans hbB⟩
    · exact Nat.coprime_div_gcd_div_gcd hg
  have hinj : Set.InjOn f (pairBox B) := by
    rintro ⟨a,b⟩ hp ⟨c,d⟩ hq heq
    have hg := congrArg Prod.fst heq
    have haq := congrArg (fun t : ℕ × NatPair => t.2.1) heq
    have hbq := congrArg (fun t : ℕ × NatPair => t.2.2) heq
    dsimp [f] at hg haq hbq
    have ha := Nat.div_mul_cancel (Nat.gcd_dvd_left a b)
    have hb := Nat.div_mul_cancel (Nat.gcd_dvd_right a b)
    have hc := Nat.div_mul_cancel (Nat.gcd_dvd_left c d)
    have hd := Nat.div_mul_cancel (Nat.gcd_dvd_right c d)
    have ha' : a=c := by
      rw [haq,hg] at ha
      exact ha.symm.trans hc
    have hb' : b=d := by
      rw [hbq,hg] at hb
      exact hb.symm.trans hd
    exact Prod.ext ha' hb' 
  have hweight : ∀ p∈pairBox B, pairWeight p=wt (f p) := by
    rintro ⟨a,b⟩ hp
    obtain ⟨ha,haB,hb,hbB⟩ := mem_pairBox.mp hp
    have hga := Nat.div_mul_cancel (Nat.gcd_dvd_left a b)
    have hgb := Nat.div_mul_cancel (Nat.gcd_dvd_right a b)
    have hgaR : ((a/Nat.gcd a b:ℕ):ℝ)*(Nat.gcd a b:ℝ)=(a:ℝ) := by exact_mod_cast hga
    have hgbR : ((b/Nat.gcd a b:ℕ):ℝ)*(Nat.gcd a b:ℝ)=(b:ℝ) := by exact_mod_cast hgb
    dsimp [wt,f,pairWeight]
    rw [one_div, one_div, one_div, ← mul_inv]
    congr 1
    rw [← hgaR, ← hgbR]
    ring
  have hsum : (∑ p∈pairBox B, pairWeight p)≤∑ t∈target, wt t := by
    calc
      (∑ p∈pairBox B, pairWeight p)=(∑ p∈pairBox B, wt (f p)) := sum_congr rfl hweight
      _ ≤ ∑ t∈target, wt t := sum_le_sum_of_injOn _ _ _ _ hmap hinj (fun t _ => by
        dsimp [wt,pairWeight]; positivity)
  have htarget : (∑ t∈target, wt t) =
      (∑ g∈Icc 1 B, 1/(g:ℝ)^2)*coprimeMass B := by
    dsimp [target,wt,coprimeMass]
    rw [sum_product]
    simp_rw [← mul_sum, ← sum_mul]
  rw [pairBox_weight, htarget] at hsum
  have hnonneg : 0≤coprimeMass B := sum_nonneg (fun p _ => pairWeight_nonneg p)
  exact hsum.trans (mul_le_mul_of_nonneg_right (reciprocal_sq_sum_le_two B) hnonneg)

lemma coprimeMass_split (B : ℕ) (hB : 1≤B) :
    coprimeMass B = 2*rayMass 1 B+1 := by
  classical
  let lo := (coprimeBox B).filter (fun p => p.1<p.2)
  let hi := (coprimeBox B).filter (fun p => p.2<p.1)
  let di := (coprimeBox B).filter (fun p => p.1=p.2)
  have hlo : lo=raySet 1 B := by
    ext p
    simp only [lo,raySet,mem_filter]
    constructor
    · rintro ⟨hp,hlt⟩
      exact ⟨hp, (mem_pairBox.mp (mem_filter.mp hp).1).1, hlt⟩
    · rintro ⟨hp,_,hlt⟩
      exact ⟨hp,hlt⟩
  have hhi : (∑ p∈hi, pairWeight p)=(∑ p∈lo, pairWeight p) := by
    refine sum_bij (fun p _ => p.swap) ?_ ?_ ?_ ?_
    · rintro ⟨a,b⟩ hp
      simp only [hi,lo,coprimeBox,pairBox,mem_filter,Finset.product_eq_sprod,Prod.swap_prod_mk,Prod.fst,Prod.snd,mem_product,mem_Icc] at hp ⊢
      exact ⟨⟨⟨hp.1.1.2,hp.1.1.1⟩,hp.1.2.symm⟩,hp.2⟩
    · intro p hp q hq h
      have h' := congrArg Prod.swap h
      simpa using h'
    · intro p hp
      refine ⟨p.swap, ?_, by simp⟩
      rcases p with ⟨a,b⟩
      simp only [hi,lo,coprimeBox,pairBox,mem_filter,Finset.product_eq_sprod,Prod.swap_prod_mk,Prod.fst,Prod.snd,mem_product,mem_Icc] at hp ⊢
      exact ⟨⟨⟨hp.1.1.2,hp.1.1.1⟩,hp.1.2.symm⟩,hp.2⟩
    · intro p hp
      dsimp [pairWeight]
      rw [mul_comm]
  have hdi : di={(1,1)} := by
    ext p
    rcases p with ⟨a,b⟩
    simp only [di,coprimeBox,pairBox,mem_filter,Finset.product_eq_sprod,Prod.swap_prod_mk,Prod.fst,Prod.snd,mem_product,mem_Icc,
      mem_singleton,Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hab,hcop⟩,heq⟩
      subst b
      have ha1 : a=1 := by simpa using hcop
      exact ⟨ha1,ha1⟩
    · rintro ⟨rfl,rfl⟩
      simp [hB]
  have hsplit : coprimeMass B=(∑ p∈lo,pairWeight p)+(∑ p∈hi,pairWeight p)+
      (∑ p∈di,pairWeight p) := by
    dsimp [coprimeMass,lo,hi,di]
    rw [sum_filter,sum_filter,sum_filter,←sum_add_distrib,←sum_add_distrib]
    apply sum_congr rfl
    intro p hp
    rcases lt_trichotomy p.1 p.2 with h|h|h
    · simp [h,h.ne,not_lt.mpr h.le]
    · simp [h]
    · simp [h,h.ne',not_lt.mpr h.le]
  rw [hsplit,hhi,hlo,hdi]
  simp only [rayMass,sum_singleton,pairWeight,Nat.cast_one,mul_one,div_one]
  ring

/-- Removing the small numerator rays costs at most a harmonic rectangle. -/
lemma rayMass_truncation (K B : ℕ) (hB : 1≤B) :
    (H B)^2/4-1/2-H (K-1)*H B ≤ rayMass K B := by
  classical
  let small := (raySet 1 B).filter (fun p => p.1<K)
  have hsplit : rayMass 1 B=rayMass K B+∑ p∈small,pairWeight p := by
    unfold rayMass
    have hlarge : (raySet 1 B).filter (fun p => K≤p.1)=raySet K B := by
      ext p
      simp only [raySet,mem_filter]
      constructor
      · rintro ⟨⟨hp,_,hlt⟩,hK⟩
        exact ⟨hp,hK,hlt⟩
      · rintro ⟨hp,hK,hlt⟩
        exact ⟨⟨hp,(mem_pairBox.mp (mem_filter.mp hp).1).1,hlt⟩,hK⟩
    rw [← hlarge]
    dsimp [small]
    rw [sum_filter,sum_filter,←sum_add_distrib]
    apply sum_congr rfl
    intro p hp
    by_cases h : K≤p.1
    · simp [h,not_lt.mpr h]
    · simp [h,lt_of_not_ge h]
  have hsmall : (∑ p∈small,pairWeight p)≤H (K-1)*H B := by
    have hsub : small ⊆ (Icc 1 (K-1)).product (Icc 1 B) := by
      rintro ⟨a,b⟩ hp
      obtain ⟨hpray,hlt⟩ := mem_filter.mp hp
      obtain ⟨hpc,_,hab⟩ := mem_filter.mp hpray
      have hpbox := mem_pairBox.mp (mem_filter.mp hpc).1
      exact mem_product.mpr ⟨mem_Icc.mpr ⟨hpbox.1,by omega⟩,
        mem_Icc.mpr ⟨hpbox.2.2.1,hpbox.2.2.2⟩⟩
    calc
      (∑ p∈small,pairWeight p)≤
          ∑ p∈(Icc 1 (K-1)).product (Icc 1 B),pairWeight p :=
        sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => pairWeight_nonneg p)
      _ = H (K-1)*H B := by
        rw [Finset.product_eq_sprod, sum_product]
        simp only [pairWeight]
        simp_rw [← one_div_mul_one_div, ← mul_sum, ← sum_mul]
        rfl
  have hcop := harmonic_square_le_two_coprimeMass B
  rw [coprimeMass_split B hB,hsplit] at hcop
  nlinarith

end
end PrimeAbundance.Analytic
