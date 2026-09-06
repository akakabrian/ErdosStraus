/- Exact finite residue counting. The error bound is valid even when q > H. -/
import PrimeAbundance.ReciprocalBlocks
import PrimeAbundance.Bonferroni

set_option autoImplicit false
open scoped Classical
open scoped BigOperators
open Finset

namespace PrimeAbundance.Analytic
noncomputable section

lemma sum_indicator_eq_card {Ω : Type*} [Fintype Ω] (P : Ω → Prop)
    [DecidablePred P] :
    (∑ ω : Ω, indicator (P ω)) = (Nat.card {ω : Ω // P ω} : ℝ) := by
  classical
  simp [indicator, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- Every full q-block supplies exactly one hit. -/
theorem residueHits_card_ge (q A H : ℕ) (hq : 0 < q) (r : ZMod q) :
    H/q ≤ Nat.card (Late.ResidueHits q A H r) := by
  classical
  letI : NeZero q := ⟨hq.ne'⟩
  let t : ℕ := (r-(A : ZMod q)).val
  have ht : t < q := ZMod.val_lt _
  let f : Fin (H/q) → Late.ResidueHits q A H r := fun i =>
    ⟨⟨i.val*q+t, by
      have hi := i.isLt
      have hmul : (i.val+1)*q ≤ (H/q)*q := Nat.mul_le_mul_right q hi
      have hdiv := Nat.div_mul_le_self H q
      nlinarith⟩, by
      dsimp [t]
      simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, add_zero,
        ZMod.natCast_zmod_val]
      ring⟩
  have hf : Function.Injective f := by
    intro i j hij
    have h := congrArg (fun x : Late.ResidueHits q A H r => x.val.val) hij
    dsimp [f] at h
    apply Fin.ext
    nlinarith
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using
    Fintype.card_le_of_injective f hf

/-- Literal plus/minus one error for every interval, including H=0 and q=1. -/
theorem residueHits_error (q A H : ℕ) (hq : 0 < q) (r : ZMod q) :
    |(Nat.card (Late.ResidueHits q A H r) : ℝ) - (H:ℝ)/(q:ℝ)| ≤ 1 := by
  letI : NeZero q := ⟨hq.ne'⟩
  have hup := Late.residueHits_card_le q A H hq r
  have hlo := residueHits_card_ge q A H hq r
  have hqR : (0:ℝ)<(q:ℝ) := by exact_mod_cast hq
  have hdiv : ((H/q : ℕ) : ℝ)*(q:ℝ) ≤ (H:ℝ) := by
    exact_mod_cast Nat.div_mul_le_self H q
  have hmod : (H:ℝ) < (((H/q : ℕ) : ℝ)+1)*(q:ℝ) := by
    have h := Nat.mod_add_div H q
    have hm := Nat.mod_lt H hq
    have hn : H < (H/q+1)*q := by nlinarith
    exact_mod_cast hn
  have hfloor : ((H/q : ℕ) : ℝ) ≤ (H:ℝ)/(q:ℝ) :=
    (le_div_iff₀ hqR).mpr hdiv
  have hceil : (H:ℝ)/(q:ℝ) < ((H/q : ℕ) : ℝ)+1 :=
    (div_lt_iff₀ hqR).mpr hmod
  have hupR : (Nat.card (Late.ResidueHits q A H r):ℝ) ≤ ((H/q:ℕ):ℝ)+1 := by
    exact_mod_cast hup
  have hloR : ((H/q:ℕ):ℝ) ≤ (Nat.card (Late.ResidueHits q A H r):ℝ) := by
    exact_mod_cast hlo
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma residue_indicator_error (q A H : ℕ) (hq : 0 < q) (r : ZMod q) :
    |(∑ i : Fin H, indicator (((A+i.val:ℕ):ZMod q)=r))-(H:ℝ)/(q:ℝ)| ≤ 1 := by
  rw [sum_indicator_eq_card]
  exact residueHits_error q A H hq r

/-- Multiplication by a unit gives one, not several, residue classes. -/
lemma linear_residue_error (c q A H : ℕ) (hq : 0 < q) (hcq : Nat.Coprime c q) :
    |(∑ i : Fin H,
        indicator ((c:ZMod q)*((A+i.val:ℕ):ZMod q)=1))-(H:ℝ)/(q:ℝ)| ≤ 1 := by
  classical
  letI : NeZero q := ⟨hq.ne'⟩
  have hc : IsUnit (c : ZMod q) := by
    rw [ZMod.isUnit_iff_coprime]
    exact hcq
  let r : ZMod q := ↑(hc.unit⁻¹)
  have hrc : r*(c:ZMod q)=1 := by
    dsimp [r]
    calc
      ↑(hc.unit⁻¹) * (c : ZMod q) = ↑(hc.unit⁻¹) * ↑hc.unit :=
        congrArg (fun z : ZMod q => ↑(hc.unit⁻¹) * z) hc.unit_spec.symm
      _ = 1 := by simp
  have hcr : (c:ZMod q)*r=1 := by rw [mul_comm]; exact hrc
  have heq : ∀ z : ZMod q, (c:ZMod q)*z=1 ↔ z=r := by
    intro z
    constructor
    · intro hz
      calc
        z = r*((c:ZMod q)*z) := by rw [← mul_assoc, hrc, one_mul]
        _ = r := by rw [hz, mul_one]
    · rintro rfl
      exact hcr
  simp_rw [heq]
  exact residue_indicator_error q A H hq r

/-- Products of distinct primes have the exact divisor-intersection property. -/
lemma prime_dvd_prod_iff_mem (s : Finset ℕ) (hs : ∀ p ∈ s, Nat.Prime p)
    (p : ℕ) (hp : Nat.Prime p) : p ∣ ∏ q ∈ s, q ↔ p ∈ s := by
  induction s using Finset.induction_on with
  | empty => simp [hp.ne_one]
  | @insert q s hq ih =>
    have hqp := hs q (mem_insert_self _ _)
    have hsp : ∀ r ∈ s, Nat.Prime r := fun r hr => hs r (mem_insert_of_mem hr)
    rw [prod_insert hq, hp.dvd_mul, ih hsp, mem_insert]
    have hdiv : p ∣ q ↔ p=q := by
      rw [Nat.dvd_prime hqp]
      simp [hp.ne_one]
    rw [hdiv]

lemma primeProduct_dvd_iff (s : Finset ℕ) (hs : ∀ p ∈ s, Nat.Prime p) (n : ℕ) :
    (∏ p ∈ s, p) ∣ n ↔ ∀ p ∈ s, p ∣ n := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    have hpp := hs p (mem_insert_self _ _)
    have hsp : ∀ q ∈ s, Nat.Prime q := fun q hq => hs q (mem_insert_of_mem hq)
    have hc : Nat.Coprime p (∏ q ∈ s, q) := by
      apply hpp.coprime_iff_not_dvd.mpr
      rwa [prime_dvd_prod_iff_mem s hsp p hpp]
    rw [prod_insert hp]
    constructor
    · intro h
      have hp' : p∣n := (dvd_mul_right p _).trans h
      have hs' : (∏ q ∈ s, q)∣n := (dvd_mul_left _ p).trans h
      simpa only [mem_insert, forall_eq_or_imp] using
        And.intro hp' ((ih hsp).mp hs')
    · intro h
      have hp' := h p (mem_insert_self _ _)
      have hs' : (∏ q ∈ s, q)∣n := (ih hsp).mpr
        (fun q hq => h q (mem_insert_of_mem hq))
      exact hc.mul_dvd_of_dvd_of_dvd hp' hs' 

lemma primeProduct_pos (s : Finset ℕ) (hs : ∀ p ∈ s, Nat.Prime p) :
    0 < ∏ p ∈ s, p := prod_pos (fun p hp => (hs p hp).pos)

lemma primeProduct_coprime (s : Finset ℕ) (c : ℕ)
    (hs : ∀ p ∈ s, Nat.Prime p ∧ ¬p∣c) :
    Nat.Coprime c (∏ p ∈ s, p) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    have hpp := hs p (mem_insert_self _ _)
    have hsp := fun q hq => hs q (mem_insert_of_mem hq)
    rw [prod_insert hp]
    exact (hpp.1.coprime_iff_not_dvd.mpr hpp.2).symm.mul_right (ih hsp)

lemma primeProduct_injective_on_powerset (s : Finset ℕ)
    (hs : ∀ p ∈ s, Nat.Prime p) :
    Set.InjOn (fun t : Finset ℕ => ∏ p ∈ t, p) s.powerset := by
  intro t ht u hu hprod
  dsimp at hprod
  apply Finset.ext
  intro p
  by_cases hp : p ∈ s
  · have hpp := hs p hp
    have htp := fun q hq => hs q ((mem_powerset.mp ht) hq)
    have hup := fun q hq => hs q ((mem_powerset.mp hu) hq)
    rw [← prime_dvd_prod_iff_mem t htp p hpp,
      ← prime_dvd_prod_iff_mem u hup p hpp, hprod]
  · have hpt : p ∉ t := fun h => hp ((mem_powerset.mp ht) h)
    have hpu : p ∉ u := fun h => hp ((mem_powerset.mp hu) h)
    simp [hpt, hpu]

/-- Uniform endpoint budget: distinct prime subsets inject into their products. -/
lemma truncated_prime_subsets_card (s : Finset ℕ) (w j : ℕ)
    (hw : 1 ≤ w) (hs : ∀ p ∈ s, Nat.Prime p ∧ p≤w) :
    ((s.powerset).filter (fun t => t.card ≤ j)).card ≤ w^j := by
  classical
  let t := (s.powerset).filter (fun t => t.card ≤ j)
  let f : Finset ℕ → ℕ := fun u => ∏ p ∈ u, p
  have hinj : Set.InjOn f t := by
    intro a ha b hb h
    exact primeProduct_injective_on_powerset s (fun p hp => (hs p hp).1)
      (mem_filter.mp ha).1 (mem_filter.mp hb).1 h
  have hmap : t.image f ⊆ Icc 1 (w^j) := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hz
    obtain ⟨has, haj⟩ := mem_filter.mp ha
    have hprime := fun p hp => (hs p ((mem_powerset.mp has) hp)).1
    refine mem_Icc.mpr ⟨primeProduct_pos a hprime, ?_⟩
    calc
      f a ≤ ∏ _p ∈ a, w := by
        apply prod_le_prod (fun _ _ => Nat.zero_le _)
        intro p hp
        exact (hs p ((mem_powerset.mp has) hp)).2
      _ = w^a.card := by simp
      _ ≤ w^j := Nat.pow_le_pow_right hw haj
  calc
    t.card = (t.image f).card := (card_image_of_injOn hinj).symm
    _ ≤ (Icc 1 (w^j)).card := card_le_card hmap
    _ = w^j := by simp

/-- A subset of excluded primes gives one residue class modulo its full product. -/
lemma prime_intersection_error (c U H : ℕ) (hc : 2 ≤ c) (s : Finset ℕ)
    (hs : ∀ p ∈ s, Nat.Prime p ∧ ¬p∣c) :
    |(∑ i : Fin H, indicator (∀ p ∈ s, p ∣ c*(U+i.val+1)-1)) -
        (H:ℝ)*(∏ p ∈ s, 1/(p:ℝ))| ≤ 1 := by
  classical
  let q : ℕ := ∏ p ∈ s, p
  have hq : 0 < q := primeProduct_pos s (fun p hp => (hs p hp).1)
  have hcq : Nat.Coprime c q := primeProduct_coprime s c hs
  letI : NeZero q := ⟨hq.ne'⟩
  have heq : ∀ i : Fin H,
      (∀ p ∈ s, p∣c*(U+i.val+1)-1) ↔
        (c:ZMod q)*((U+1+i.val:ℕ):ZMod q)=1 := by
    intro i
    rw [← primeProduct_dvd_iff s (fun p hp => (hs p hp).1)]
    change q ∣ c*(U+i.val+1)-1 ↔ _
    rw [← ZMod.natCast_eq_zero_iff]
    have hprod : 1 ≤ c*(U+i.val+1) := by nlinarith
    rw [Nat.cast_sub hprod, Nat.cast_mul, Nat.cast_one, sub_eq_zero]
    rw [show U+i.val+1 = U+1+i.val by omega]
  simp_rw [heq]
  have hprod : (∏ p ∈ s, 1/(p:ℝ)) = 1/(q:ℝ) := by
    dsimp [q]
    simp only [one_div, Nat.cast_prod, prod_inv_distrib]
  rw [hprod]
  simpa only [div_eq_mul_inv, one_div, one_mul] using
    linear_residue_error c q (U+1) H hq hcq

end
end PrimeAbundance.Analytic
