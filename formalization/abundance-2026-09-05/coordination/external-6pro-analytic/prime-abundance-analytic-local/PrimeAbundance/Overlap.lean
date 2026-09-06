/- Concrete unordered overlap bound for delayed packets.
The common-divisor cover keeps every prime-power exponent. -/
import PrimeAbundance.DivisorKernel
import PrimeAbundance.DeterminantMoment

set_option autoImplicit false
open scoped Classical
open scoped BigOperators
open Finset

namespace PrimeAbundance.Analytic
noncomputable section

abbrev Ray := ℕ × ℕ

def rays (B : ℕ) : Finset Ray := raySet (Late.rayCutoff B) B
def scales (B : ℕ) : Finset ℕ := Ioc (B^4) (B^6)
def unpack (r : Ray) (u : ℕ) : Late.Param := (r.1,r.2,u)

def overlapTerm (t z : Late.Param) : ℝ :=
  let q := qForm t.1 t.2.1 t.2.2
  let q' := qForm z.1 z.2.1 z.2.2
  let g := Nat.gcd q q'
  if q<q' ∧ 1<g ∧ Nat.ModEq g (Late.label t.1 t.2.2) (Late.label z.1 z.2.2)
  then (g:ℝ)/((q:ℝ)*(q':ℝ)) else 0

lemma overlapTerm_nonneg (t z : Late.Param) : 0≤overlapTerm t z := by
  simp only [overlapTerm]
  split_ifs <;> positivity

lemma overlap_eq_parameters (B : ℕ) :
    Late.overlap B=∑ t∈Late.parameters B,∑ z∈Late.parameters B,overlapTerm t z := by
  classical
  unfold Late.overlap Late.packets
  have hinj : Set.InjOn Late.encode (Late.parameters B) := by
    intro t ht z hz he
    apply Late.encode_injOn B
    · exact (mem_filter.mp ht).2
    · exact (mem_filter.mp hz).2
    · exact he
  rw [sum_image hinj]
  apply sum_congr rfl
  intro t ht
  rw [sum_image hinj]
  apply sum_congr rfl
  intro z hz
  rcases t with ⟨a,b,u⟩
  rcases z with ⟨c,e,v⟩
  simp only [qForm_encode,overlapTerm]
  rfl

lemma ray_membership {B : ℕ} {r : Ray} (hr : r∈rays B) :
    0<r.1 ∧ r.1<r.2 ∧ r.2≤B ∧ Nat.Coprime r.1 r.2 := by
  obtain ⟨hc,hK,hlt⟩ := mem_filter.mp hr
  obtain ⟨hbox,hcop⟩ := mem_filter.mp hc
  have hb := mem_pairBox.mp hbox
  exact ⟨hb.1,hlt,hb.2.2.2,hcop⟩

lemma parameter_ray_scale {B : ℕ} {t : Late.Param} (ht : t∈Late.parameters B) :
    (t.1,t.2.1)∈rays B ∧ t.2.2∈scales B := by
  obtain ⟨hB,hK,hab,hbB,hcop,huL,huU,hr⟩ := (mem_filter.mp ht).2
  have hK2 : 2≤Late.rayCutoff B := by dsimp [Late.rayCutoff]; omega
  refine ⟨mem_filter.mpr ⟨mem_filter.mpr ⟨?_,hcop⟩,hK,hab⟩,mem_Ioc.mpr ⟨huL,huU⟩⟩
  exact mem_pairBox.mpr ⟨by omega,hab.le.trans hbB,by omega,hbB⟩

/-- Enlarge retained parameters only after obtaining a nonnegative pointwise cover. -/
lemma sum_parameters_le (B : ℕ) (F : Late.Param → ℝ) (hF : ∀ t,0≤F t) :
    (∑ t∈Late.parameters B,F t)≤∑ r∈rays B,∑ u∈scales B,F (unpack r u) := by
  classical
  let f : Late.Param → Ray × ℕ := fun t => ((t.1,t.2.1),t.2.2)
  let wt : Ray × ℕ → ℝ := fun z => F (unpack z.1 z.2)
  have hmap : ∀ t∈Late.parameters B,f t∈(rays B).product (scales B) := by
    intro t ht
    exact mem_product.mpr (parameter_ray_scale ht)
  have hinj : Set.InjOn f (Late.parameters B) := by
    rintro ⟨a,b,u⟩ ht ⟨c,e,v⟩ hz h
    simp only [f,Prod.mk.injEq] at h ⊢
    tauto
  have h := sum_le_sum_of_injOn (Late.parameters B) ((rays B).product (scales B)) f wt
    hmap hinj (fun z _ => hF (unpack z.1 z.2))
  calc
    _ ≤ ∑ z∈(rays B).product (scales B),F (unpack z.1 z.2) := by
      simpa only [f,wt] using h
    _ = _ := Finset.sum_product (rays B) (scales B)
      (fun z : Ray × ℕ => F (unpack z.1 z.2))

lemma sum_parameter_pairs_le (B : ℕ) (F : Late.Param → Late.Param → ℝ)
    (hF : ∀ t z,0≤F t z) :
    (∑ t∈Late.parameters B,∑ z∈Late.parameters B,F t z)≤
      ∑ r∈rays B,∑ s∈rays B,∑ u∈scales B,∑ v∈scales B,F (unpack r u) (unpack s v) := by
  calc
    _ ≤ ∑ t∈Late.parameters B,∑ s∈rays B,∑ v∈scales B,F t (unpack s v) :=
      sum_le_sum (fun t _ => sum_parameters_le B (F t) (hF t))
    _ ≤ ∑ r∈rays B,∑ u∈scales B,∑ s∈rays B,∑ v∈scales B,F (unpack r u) (unpack s v) :=
      sum_parameters_le B _ (fun t => sum_nonneg (fun s _ => sum_nonneg (fun v _ => hF t _)))
    _ = _ := by
      apply sum_congr rfl
      intro r hr
      rw [sum_comm]

lemma gcd_le_twice_nontrivial_totient (g : ℕ) (hg : 1<g) :
    (g:ℝ)≤2*(∑ d∈g.divisors,if 1<d then (Nat.totient d:ℝ) else 0) := by
  have h1 : 1∈g.divisors := Nat.mem_divisors.mpr ⟨one_dvd g,by omega⟩
  have hsum : (∑ d∈g.divisors,if 1<d then (Nat.totient d:ℝ) else 0)=(g:ℝ)-1 := by
    have he : (∑ d∈g.divisors,(Nat.totient d:ℝ))=(g:ℝ) := by
      exact_mod_cast Nat.sum_totient g
    -- Split off the divisor one pointwise before summing. All divisors remain present.
    have hpoint : ∀ d∈g.divisors, (Nat.totient d:ℝ) =
        (if d=1 then (1:ℝ) else 0) +
          (if 1<d then (Nat.totient d:ℝ) else 0) := by
      intro d hd
      have hd0 := Nat.pos_of_mem_divisors hd
      by_cases hd1 : d=1
      · subst d
        norm_num
      · have hdgt : 1<d := by omega
        simp only [hd1,hdgt,if_false,if_true,zero_add]
    have hsplit := sum_congr rfl hpoint
    have hone : (∑ d∈g.divisors,if d=1 then (1:ℝ) else 0)=1 := by
      simp [h1]
    rw [sum_add_distrib,hone,he] at hsplit
    linarith
  rw [hsum]
  have hgR : (2:ℝ)≤(g:ℝ) := by exact_mod_cast hg
  linarith

def sameCover (t z : Late.Param) : ℝ :=
  if (t.1,t.2.1)=(z.1,z.2.1) ∧ t.2.2<z.2.2 then
    (Nat.gcd (qForm t.1 t.2.1 t.2.2) (qForm z.1 z.2.1 z.2.2):ℝ)/
      ((qForm t.1 t.2.1 t.2.2:ℝ)*(qForm z.1 z.2.1 z.2.2:ℝ)) else 0

def diffCover (w : ℕ) (t z : Late.Param) : ℝ :=
  if (t.1,t.2.1)=(z.1,z.2.1) then 0 else
    2*(∑ d∈(gap (t.1*z.2.1) (z.1*t.2.1)).divisors,
      if w<d ∧ d∣qForm t.1 t.2.1 t.2.2 ∧ d∣qForm z.1 z.2.1 z.2.2 then
        (Nat.totient d:ℝ)/((qForm t.1 t.2.1 t.2.2:ℝ)*(qForm z.1 z.2.1 z.2.2:ℝ))
      else 0)

lemma sameCover_nonneg (t z : Late.Param) : 0≤sameCover t z := by
  unfold sameCover
  split_ifs <;> positivity
lemma diffCover_nonneg (w : ℕ) (t z : Late.Param) : 0≤diffCover w t z := by
  unfold diffCover
  split_ifs
  · rfl
  · apply mul_nonneg (by norm_num)
    exact sum_nonneg (fun d _ => by split_ifs <;> positivity)

/-- The comparison uses roughness only to force each occurring nontrivial divisor above w. -/
lemma overlapTerm_le_cover (B : ℕ) (t z : Late.Param)
    (ht : t∈Late.parameters B) (hz : z∈Late.parameters B) :
    overlapTerm t z≤sameCover t z+diffCover (Late.cutoff (B^8)) t z := by
  classical
  rcases t with ⟨a,b,u⟩
  rcases z with ⟨c,e,v⟩
  have hrt := (parameter_ray_scale ht).1
  have hrz := (parameter_ray_scale hz).1
  obtain ⟨ha,hab,hbB,hcop⟩ := ray_membership hrt
  obtain ⟨hc,hce,heB,hcop'⟩ := ray_membership hrz
  have hb : 0<b := ha.trans hab
  have he : 0<e := hc.trans hce
  have hu : 0<u := lt_of_le_of_lt (Nat.zero_le _) (mem_Ioc.mp (parameter_ray_scale ht).2).1
  have hv : 0<v := lt_of_le_of_lt (Nat.zero_le _) (mem_Ioc.mp (parameter_ray_scale hz).2).1
  let q := qForm a b u
  let q' := qForm c e v
  let g := Nat.gcd q q'
  have hq : 0<q := qForm_pos ha hb hu
  have hq' : 0<q' := qForm_pos hc he hv
  have hden : (0:ℝ)<(q:ℝ)*(q':ℝ) := by positivity
  by_cases hfire : q<q' ∧ 1<g ∧ Nat.ModEq g (Late.label a u) (Late.label c v)
  · have hleft : overlapTerm (a,b,u) (c,e,v)=(g:ℝ)/((q:ℝ)*(q':ℝ)) := by
      simp [overlapTerm,q,q',g,hfire]
    rw [hleft]
    by_cases hrs : (a,b)=(c,e)
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj hrs
      have huv : u<v := by
        have hQ := hfire.1
        dsimp [q,q',qForm] at hQ
        have hprod : 0<12*a*b := by positivity
        nlinarith [Nat.sub_add_cancel (show 1≤12*a*b*u from Nat.mul_pos hprod hu),
          Nat.sub_add_cancel (show 1≤12*a*b*v from Nat.mul_pos hprod hv)]
      simp [sameCover,diffCover,unpack,q,q',g,hrs,huv]
    · have hDne : (a:ℤ)*(e:ℤ)-(c:ℤ)*(b:ℤ)≠0 :=
        Late.determinant_ne_zero a b c e ha hc hcop hcop' hrs
      have hDpos : 0<gap (a*e) (c*b) := by
        apply gap_pos
        intro h
        apply hDne
        exact sub_eq_zero.mpr (by exact_mod_cast h)
      have hgq : g∣q := Nat.gcd_dvd_left q q'
      have hgq' : g∣q' := Nat.gcd_dvd_right q q'
      have hlabel : (g:ℤ)∣(Late.label a u:ℤ)-(Late.label c v:ℤ) := by
        obtain ⟨k,hk⟩ := hfire.2.2.dvd
        refine ⟨-k,?_⟩
        nlinarith
      have hgc : (g:ℤ)∣Late.modulus a b u := by
        rw [←qForm_cast_int ha hb hu]
        exact_mod_cast hgq
      have hgc' : (g:ℤ)∣Late.modulus c e v := by
        rw [←qForm_cast_int hc he hv]
        exact_mod_cast hgq'
      have hD : g∣gap (a*e) (c*b) := by
        rw [nat_dvd_gap_iff]
        have h := (Late.full_modulus_compatibility a b c e u v g hgc hgc').mp
          (by simpa [Late.label,Late.intLabel] using hlabel)
        simpa only [Nat.cast_mul] using h
      have hrough : Late.cutoff (B^8)<Nat.minFac q := by
        simpa [q,qForm_encode] using (mem_filter.mp ht).2.2.2.2.2.2.2.2
      have hsub : g.divisors.filter (fun d => 1<d) ⊆
          (gap (a*e) (c*b)).divisors.filter
            (fun d => Late.cutoff (B^8)<d ∧ d∣q ∧ d∣q') := by
        intro d hd
        obtain ⟨hdg,hd1⟩ := mem_filter.mp hd
        have hdg' := (Nat.mem_divisors.mp hdg).1
        have hdq := hdg'.trans hgq
        have hdq' := hdg'.trans hgq'
        have hwd := hrough.trans_le (Nat.minFac_le_of_dvd hd1 hdq)
        exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdg'.trans hD,hDpos.ne'⟩,hwd,hdq,hdq'⟩
      have hsum := sum_le_sum_of_subset_of_nonneg hsub
        (fun d _ _ => (by positivity : (0:ℝ)≤(Nat.totient d:ℝ)))
      have hg := gcd_le_twice_nontrivial_totient g hfire.2.1
      rw [←sum_filter] at hg
      have hbound : (g:ℝ)≤2*(∑ d∈(gap (a*e) (c*b)).divisors,
          if Late.cutoff (B^8)<d ∧ d∣q ∧ d∣q' then (Nat.totient d:ℝ) else 0) := by
        rw [←sum_filter]
        linarith
      have hdiv := div_le_div_of_nonneg_right hbound hden.le
      simpa only [sameCover,diffCover,hrs,if_false,false_and,add_zero,zero_add,
        mul_div_assoc,sum_div,ite_div,zero_div,q,q',g] using hdiv
  · have h0 : overlapTerm (a,b,u) (c,e,v)=0 := by
      simp [overlapTerm,q,q',g,hfire]
    rw [h0]
    exact add_nonneg (sameCover_nonneg _ _) (diffCover_nonneg _ _ _)

lemma sameCover_scale_sum (B : ℕ) (r s : Ray) (hr : r∈rays B) (hs : s∈rays B) :
    (∑ u∈scales B,∑ v∈scales B,sameCover (unpack r u) (unpack s v)) =
      if r=s then gcdKernel (12*r.1*r.2) (B^4) (B^6) else 0 := by
  classical
  by_cases h : r=s
  · subst s
    simp only [sameCover,unpack,Prod.mk.eta,true_and,if_true]
    unfold gcdKernel scales
    apply sum_congr rfl
    intro u hu
    have hset : (Ioc (B^4) (B^6)).filter (fun v => u<v)=Ioc u (B^6) := by
      ext v
      have hui := mem_Ioc.mp hu
      simp only [mem_filter,mem_Ioc]
      omega
    rw [←sum_filter,hset]
    rfl
  · simp [sameCover,unpack,h]

lemma diffCover_scale_sum (B w : ℕ) (r s : Ray) (hrs : r≠s) :
    (∑ u∈scales B,∑ v∈scales B,diffCover w (unpack r u) (unpack s v)) =
      2*(∑ d∈(gap (r.1*s.2) (s.1*r.2)).divisors,
        if w<d then (Nat.totient d:ℝ)*
          scaleAP r.1 r.2 d (B^4) (B^6)*scaleAP s.1 s.2 d (B^4) (B^6) else 0) := by
  classical
  simp only [diffCover,unpack,Prod.mk.eta,hrs,if_false]
  simp_rw [←mul_sum]
  congr 1
  -- The summation order is u,v,d. Move d all the way outside; a single
  -- `sum_comm` would merely interchange the two scale variables.
  rw [sum_rotate_three]
  apply sum_congr rfl
  intro d hd
  by_cases hwd : w<d
  · simp only [hwd,true_and,if_true]
    let f : ℕ → ℝ := fun u =>
      if d∣qForm r.1 r.2 u then scaleWeight r.1 r.2 u else 0
    let g : ℕ → ℝ := fun v =>
      if d∣qForm s.1 s.2 v then scaleWeight s.1 s.2 v else 0
    have hf : scaleAP r.1 r.2 d (B^4) (B^6) = ∑ u∈scales B, f u := by
      rfl
    have hg : scaleAP s.1 s.2 d (B^4) (B^6) = ∑ v∈scales B, g v := by
      rfl
    rw [hf, hg]
    calc
      _ = ∑ u∈scales B, ∑ v∈scales B, (Nat.totient d:ℝ)*(f u*g v) := by
        apply sum_congr rfl
        intro u hu
        apply sum_congr rfl
        intro v hv
        by_cases hdu : d∣qForm r.1 r.2 u <;>
          by_cases hdv : d∣qForm s.1 s.2 v <;>
            simp [f,g,scaleWeight,hdu,hdv] <;> ring
      _ = (Nat.totient d:ℝ)*
          ((∑ u∈scales B, f u)*(∑ v∈scales B, g v)) := by
        rw [Finset.sum_mul_sum]
        simp only [Finset.mul_sum]
      _ = (Nat.totient d:ℝ)*(∑ u∈scales B, f u)*(∑ v∈scales B, g v) := by
        ring
  · simp [hwd]

lemma ray_determinant_pos {B : ℕ} {r s : Ray} (hr : r∈rays B) (hs : s∈rays B) (hrs : r≠s) :
    0<gap (r.1*s.2) (s.1*r.2) := by
  obtain ⟨ha,hab,hbB,hcop⟩ := ray_membership hr
  obtain ⟨hc,hce,heB,hcop'⟩ := ray_membership hs
  apply gap_pos
  intro h
  obtain ⟨ha',hb'⟩ := Late.reduced_ray_unique r.1 r.2 s.1 s.2 ha hc hcop hcop' h
  exact hrs (Prod.ext ha' hb')

lemma ray_determinant_lt {B : ℕ} {r s : Ray} (hr : r∈rays B) (hs : s∈rays B) :
    gap (r.1*s.2) (s.1*r.2)<B^2 := by
  obtain ⟨ha,hab,hbB,hcop⟩ := ray_membership hr
  obtain ⟨hc,hce,heB,hcop'⟩ := ray_membership hs
  have habound : r.1*s.2≤B^2 := by nlinarith [Nat.mul_le_mul (hab.le.trans hbB) heB]
  have hcbound : s.1*r.2≤B^2 := by nlinarith [Nat.mul_le_mul (hce.le.trans heB) hbB]
  have hp : 0<r.1*s.2 := Nat.mul_pos ha (hc.trans hce)
  have hq : 0<s.1*r.2 := Nat.mul_pos hc (ha.trans hab)
  unfold gap
  split_ifs <;> omega

def rayEnergy (r s : Ray) : ℝ :=
  if r.1*s.2=s.1*r.2 then 0 else
    (tau (gap (r.1*s.2) (s.1*r.2)):ℝ)/
      ((r.1:ℝ)*(r.2:ℝ)*(s.1:ℝ)*(s.2:ℝ))

lemma rayEnergy_nonneg (r s : Ray) : 0≤rayEnergy r s := by
  simp only [rayEnergy]
  split_ifs <;> positivity

lemma diffCover_pair_bound (n w : ℕ) (hw : 2≤w) (r s : Ray)
    (hr : r∈rays (2^n)) (hs : s∈rays (2^n)) :
    (∑ u∈scales (2^n),∑ v∈scales (2^n),diffCover w (unpack r u) (unpack s v))≤
      32*(n:ℝ)^2/(w:ℝ)*rayEnergy r s := by
  classical
  by_cases hrs : r=s
  · subst s
    simp [diffCover,unpack,rayEnergy]
  obtain ⟨ha,hab,hbB,hcop⟩ := ray_membership hr
  obtain ⟨hc,hce,heB,hcop'⟩ := ray_membership hs
  have hb := ha.trans hab
  have he := hc.trans hce
  have hD0 := ray_determinant_pos hr hs hrs
  have hDlt := ray_determinant_lt hr hs
  have hB1 : 1≤2^n := Nat.one_le_two_pow
  have hBpow : (2^n)^2≤(2^n)^4 := Nat.pow_le_pow_right hB1 (by decide)
  have hneq : r.1*s.2≠s.1*r.2 := by
    intro h
    unfold gap at hD0
    simp [h] at hD0
  rw [diffCover_scale_sum _ _ _ _ hrs,rayEnergy,if_neg hneq]
  let den : ℝ := (r.1:ℝ)*(r.2:ℝ)*(s.1:ℝ)*(s.2:ℝ)
  have hden : 0<den := by dsimp [den]; positivity
  have hwR : (0:ℝ)<(w:ℝ) := by positivity
  have hlocal : ∀ d∈(gap (r.1*s.2) (s.1*r.2)).divisors,
      (if w<d then (Nat.totient d:ℝ)*scaleAP r.1 r.2 d ((2^n)^4) ((2^n)^6)*
        scaleAP s.1 s.2 d ((2^n)^4) ((2^n)^6) else 0)≤
        16*(n:ℝ)^2/(w:ℝ)/den := by
    intro d hd
    by_cases hwd : w<d
    · rw [if_pos hwd]
      have hd0 := Nat.pos_of_mem_divisors hd
      have hdbound := (Nat.le_of_dvd hD0 (Nat.mem_divisors.mp hd).1).trans (hDlt.le.trans hBpow)
      have h1 := scaleAP_dyadic n r.1 r.2 d ha hb hd0 hdbound
      have h2 := scaleAP_dyadic n s.1 s.2 d hc he hd0 hdbound
      have hn1 : 0≤scaleAP r.1 r.2 d ((2^n)^4) ((2^n)^6) := by
        unfold scaleAP
        exact sum_nonneg (fun u _ => by
          split_ifs
          · exact scaleWeight_nonneg _ _ _
          · positivity)
      have hn2 : 0≤scaleAP s.1 s.2 d ((2^n)^4) ((2^n)^6) := by
        unfold scaleAP
        exact sum_nonneg (fun u _ => by
          split_ifs
          · exact scaleWeight_nonneg _ _ _
          · positivity)
      have ht : (Nat.totient d:ℝ)≤(d:ℝ) := by exact_mod_cast Nat.totient_le d
      calc
        _ ≤ (d:ℝ)*(4*(n:ℝ)/(11*(r.1:ℝ)*(r.2:ℝ)*(d:ℝ)))*
            (4*(n:ℝ)/(11*(s.1:ℝ)*(s.2:ℝ)*(d:ℝ))) := by
          apply mul_le_mul
          · exact mul_le_mul ht h1 hn1 (by positivity)
          · exact h2
          · exact hn2
          · positivity
        _ = 16*(n:ℝ)^2/(121*(d:ℝ)*den) := by
          have hdR : (d:ℝ)≠0 := by positivity
          dsimp [den]
          field_simp
          ring
        _ ≤ 16*(n:ℝ)^2/((w:ℝ)*den) := by
          apply div_le_div_of_nonneg_left (by positivity) (mul_pos hwR hden)
          have hwdR : (w:ℝ)≤(d:ℝ) := by exact_mod_cast hwd.le
          nlinarith [mul_le_mul_of_nonneg_right hwdR hden.le]
        _ = _ := by ring
    · rw [if_neg hwd]
      positivity
  have hsum := sum_le_sum hlocal
  have hm := mul_le_mul_of_nonneg_left hsum (by norm_num : (0:ℝ)≤2)
  have hright : 2*(∑ _d∈(gap (r.1*s.2) (s.1*r.2)).divisors,
        16*(n:ℝ)^2/(w:ℝ)/den) =
      32*(n:ℝ)^2/(w:ℝ)*((tau (gap (r.1*s.2) (s.1*r.2)):ℝ)/den) := by
    simp only [sum_const,nsmul_eq_mul,tau]
    ring
  rw [hright] at hm
  exact hm

/-- Product-factor regrouping. The fiber has at most τ(x)τ(y) factorizations. -/
lemma rayEnergy_box_le (B : ℕ) :
    (∑ r∈pairBox B,∑ s∈pairBox B,rayEnergy r s)≤determinantEnergy (B^2) := by
  classical
  let source := ((pairBox B).product (pairBox B)).filter
    (fun z => z.1.1*z.2.2≠z.2.1*z.1.2)
  let outer := ((pairBox (B^2)).filter (fun z => z.1≠z.2))
  let target := outer.sigma (fun xy => xy.1.divisors.product xy.2.divisors)
  let f : Ray × Ray → (Σ _xy:Ray,Ray) := fun z =>
    ⟨(z.1.1*z.2.2,z.2.1*z.1.2),(z.1.1,z.2.1)⟩
  let wt : (Σ _xy:Ray,Ray) → ℝ := fun z =>
    (tau (gap z.1.1 z.1.2):ℝ)/((z.1.1:ℝ)*(z.1.2:ℝ))
  have hmap : ∀ z∈source,f z∈target := by
    rintro ⟨⟨a,b⟩,⟨c,e⟩⟩ hz
    obtain ⟨hzbox,hne⟩ := mem_filter.mp hz
    obtain ⟨hr,hs⟩ := mem_product.mp hzbox
    obtain ⟨ha,haB,hb,hbB⟩ := mem_pairBox.mp hr
    obtain ⟨hc,hcB,he,heB⟩ := mem_pairBox.mp hs
    refine mem_sigma.mpr ⟨mem_filter.mpr ⟨?_,hne⟩,?_⟩
    · exact mem_pairBox.mpr ⟨Nat.mul_pos ha he,by nlinarith [Nat.mul_le_mul haB heB],
        Nat.mul_pos hc hb,by nlinarith [Nat.mul_le_mul hcB hbB]⟩
    · exact mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨dvd_mul_right a e,by positivity⟩,
        Nat.mem_divisors.mpr ⟨dvd_mul_right c b,by positivity⟩⟩
  have hinj : Set.InjOn f source := by
    rintro ⟨⟨a,b⟩,⟨c,e⟩⟩ hz ⟨⟨a',b'⟩,⟨c',e'⟩⟩ hz' h
    have hxy := congrArg Sigma.fst h
    have hab := congrArg Sigma.snd h
    have ha : a=a' := congrArg Prod.fst hab
    have hc : c=c' := congrArg Prod.snd hab
    subst a'
    subst c'
    have hx : a*e=a*e' := congrArg Prod.fst hxy
    have hy : c*b=c*b' := congrArg Prod.snd hxy
    have hbox := mem_product.mp (mem_filter.mp hz).1
    have ha0 := (mem_pairBox.mp hbox.1).1
    have hc0 := (mem_pairBox.mp hbox.2).1
    have hb : b=b' := by nlinarith
    have he : e=e' := by nlinarith
    subst b'
    subst e'
    rfl
  have hsource : (∑ r∈pairBox B,∑ s∈pairBox B,rayEnergy r s)=∑ z∈source,wt (f z) := by
    rw [←Finset.sum_product (pairBox B) (pairBox B)
      (fun z : Ray × Ray => rayEnergy z.1 z.2)]
    dsimp [source]
    rw [sum_filter]
    apply sum_congr rfl
    intro z hz
    dsimp [wt,f,rayEnergy]
    split_ifs <;> push_cast <;> ring
  have htarget : (∑ z∈target,wt z)=determinantEnergy (B^2) := by
    dsimp [target,wt]
    rw [sum_sigma]
    simp only [sum_product,sum_const,nsmul_eq_mul]
    unfold determinantEnergy
    dsimp [outer,pairBox]
    rw [sum_filter]
    apply sum_congr rfl
    intro xy hxy
    dsimp [energyWeight,tau]
    by_cases h : xy.1=xy.2 <;> simp [h] <;> ring
  rw [hsource,←htarget]
  exact sum_le_sum_of_injOn source target f wt hmap hinj (fun z _ => by dsimp [wt]; positivity)

lemma rayEnergy_rays_le (B : ℕ) :
    (∑ r∈rays B,∑ s∈rays B,rayEnergy r s)≤determinantEnergy (B^2) := by
  have hsub : rays B⊆pairBox B := fun r hr => (mem_filter.mp (mem_filter.mp hr).1).1
  calc
    _ ≤ ∑ r∈rays B,∑ s∈pairBox B,rayEnergy r s := by
      apply sum_le_sum
      intro r hr
      exact sum_le_sum_of_subset_of_nonneg hsub (fun s _ _ => rayEnergy_nonneg r s)
    _ ≤ ∑ r∈pairBox B,∑ s∈pairBox B,rayEnergy r s :=
      sum_le_sum_of_subset_of_nonneg hsub
        (fun r _ _ => sum_nonneg (fun s _ => rayEnergy_nonneg r s))
    _ ≤ _ := rayEnergy_box_le B

lemma same_ray_sum_bound (n : ℕ) (hn : 3≤n) :
    (∑ r∈rays (2^n),gcdKernel (12*r.1*r.2) ((2^n)^4) ((2^n)^6))≤
      1536*((n+1:ℕ):ℝ)^3 := by
  have hB8 : 8≤2^n := by simpa using Nat.pow_le_pow_right (by decide : 1≤2) hn
  have hdelay : ∀ r∈rays (2^n),2*(12*r.1*r.2)≤(2^n)^4 := by
    intro r hr
    obtain ⟨ha,hab,hbB,hcop⟩ := ray_membership hr
    have hp := Nat.mul_le_mul (hab.le.trans hbB) hbB
    have hB2 : 24≤(2^n)^2 := by nlinarith
    nlinarith [Nat.mul_le_mul_left ((2^n)^2) hB2]
  have hsum : (∑ r∈rays (2^n),gcdKernel (12*r.1*r.2) ((2^n)^4) ((2^n)^6))≤
      384*((n+1:ℕ):ℝ)^3*(∑ r∈rays (2^n),1/((r.1:ℝ)^2*(r.2:ℝ)^2)) := by
    rw [mul_sum]
    apply sum_le_sum
    intro r hr
    obtain ⟨ha,hab,hbB,hcop⟩ := ray_membership hr
    have hb := ha.trans hab
    have h := gcdKernel_delayed n (12*r.1*r.2) (by nlinarith [Nat.mul_pos ha hb]) (hdelay r hr)
    have hden : (r.1:ℝ)^2*(r.2:ℝ)^2≤((12*r.1*r.2:ℕ):ℝ)^2 := by
      push_cast
      nlinarith [sq_nonneg ((r.1:ℝ)*(r.2:ℝ))]
    exact h.trans (by
      rw [mul_one_div]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden)
  have hsquares : (∑ r∈rays (2^n),1/((r.1:ℝ)^2*(r.2:ℝ)^2))≤4 := by
    have hsub : rays (2^n)⊆pairBox (2^n) := fun r hr =>
      (mem_filter.mp (mem_filter.mp hr).1).1
    calc
      _ ≤ ∑ r∈pairBox (2^n),1/((r.1:ℝ)^2*(r.2:ℝ)^2) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun r _ _ => by positivity)
      _ = (∑ a∈Icc (1:ℕ) (2^n),1/(a:ℝ)^2)^2 := by
        rw [pairBox]
        calc
          _ = ∑ a∈Icc (1:ℕ) (2^n),∑ b∈Icc (1:ℕ) (2^n),
              1/((a:ℝ)^2*(b:ℝ)^2) := Finset.sum_product _ _ _
          _ = _ := by
            simp_rw [←one_div_mul_one_div,←mul_sum,←sum_mul]
            simp only [pow_two]
      _ ≤ 4 := by
        have hb := reciprocal_sq_sum_le_two (2^n)
        have h0 : (0:ℝ)≤∑ a∈Icc (1:ℕ) (2^n),1/(a:ℝ)^2 := by positivity
        nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hsquares (by positivity : (0:ℝ)≤384*((n+1:ℕ):ℝ)^3)]

/-- Concrete finite overlap estimate. The cutoff is the actual project cutoff. -/
theorem overlap_dyadic_finite (n : ℕ) (hn : 3≤n) (hw : 2≤Late.cutoff ((2^n)^8)) :
    Late.overlap (2^n)≤1536*((n+1:ℕ):ℝ)^3+
      131072*((n+1:ℕ):ℝ)^11/(Late.cutoff ((2^n)^8):ℝ) := by
  classical
  let B := 2^n
  let w := Late.cutoff (B^8)
  have hcover : Late.overlap B≤∑ t∈Late.parameters B,∑ z∈Late.parameters B,
      (sameCover t z+diffCover w t z) := by
    rw [overlap_eq_parameters]
    apply sum_le_sum
    intro t ht
    exact sum_le_sum (fun z hz => overlapTerm_le_cover B t z ht hz)
  have henlarge := sum_parameter_pairs_le B (fun t z => sameCover t z+diffCover w t z)
    (fun t z => add_nonneg (sameCover_nonneg t z) (diffCover_nonneg w t z))
  have hsame : (∑ r∈rays B,∑ s∈rays B,∑ u∈scales B,∑ v∈scales B,
      sameCover (unpack r u) (unpack s v))=
      ∑ r∈rays B,gcdKernel (12*r.1*r.2) (B^4) (B^6) := by
    apply sum_congr rfl
    intro r hr
    simp_rw [sum_congr rfl (fun s hs => sameCover_scale_sum B r s hr hs)]
    simp [hr]
  have hdiff : (∑ r∈rays B,∑ s∈rays B,∑ u∈scales B,∑ v∈scales B,
      diffCover w (unpack r u) (unpack s v))≤
      131072*((n+1:ℕ):ℝ)^11/(w:ℝ) := by
    calc
      _ ≤ ∑ r∈rays B,∑ s∈rays B,32*(n:ℝ)^2/(w:ℝ)*rayEnergy r s := by
        apply sum_le_sum
        intro r hr
        exact sum_le_sum (fun s hs => diffCover_pair_bound n w hw r s hr hs)
      _ = 32*(n:ℝ)^2/(w:ℝ)*(∑ r∈rays B,∑ s∈rays B,rayEnergy r s) := by
        simp_rw [←mul_sum]
      _ ≤ 32*(n:ℝ)^2/(w:ℝ)*determinantEnergy (B^2) :=
        mul_le_mul_of_nonneg_left (rayEnergy_rays_le B) (by positivity)
      _ ≤ 32*(n:ℝ)^2/(w:ℝ)*(4096*((n+1:ℕ):ℝ)^9) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [B,←pow_mul,mul_comm n 2] using determinantEnergy_dyadic n
      _ ≤ 131072*((n+1:ℕ):ℝ)^11/(w:ℝ) := by
        have hnle : (n:ℝ)≤((n+1:ℕ):ℝ) := by exact_mod_cast Nat.le_succ n
        have hp := pow_le_pow_left₀ (by positivity : (0:ℝ)≤(n:ℝ)) hnle 2
        have hm := mul_le_mul_of_nonneg_right hp
          (by positivity : (0:ℝ)≤131072*((n+1:ℕ):ℝ)^9/(w:ℝ))
        convert hm using 1 <;> ring
  have htot := hcover.trans henlarge
  simp_rw [sum_add_distrib] at htot
  rw [hsame] at htot
  have hs := same_ray_sum_bound n hn
  dsimp [B,w] at *
  linarith

end
end PrimeAbundance.Analytic
