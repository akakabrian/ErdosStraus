/- Exact scale/packet sums, and dyadic progression estimates. -/
import PrimeAbundance.Sieve
import PrimeAbundance.RayMass
import PrimeAbundance.Packets

set_option autoImplicit false
open scoped Classical
open scoped BigOperators
open Finset

namespace PrimeAbundance.Analytic
noncomputable section

/-- The row modulus in parameter coordinates; natural subtraction is justified below. -/
def qForm (a b u : ℕ) : ℕ := 12*a*b*u-1

def scaleWeight (a b u : ℕ) : ℝ := 1/(qForm a b u:ℝ)
def keptScaleWeight (a b w u : ℕ) : ℝ :=
  if w<Nat.minFac (qForm a b u) then scaleWeight a b u else 0

def scaleAP (a b d L T : ℕ) : ℝ :=
  ∑ u∈Ioc L T, if d∣qForm a b u then scaleWeight a b u else 0

lemma qForm_pos {a b u : ℕ} (ha : 0<a) (hb : 0<b) (hu : 0<u) : 0<qForm a b u := by
  dsimp [qForm]
  have h : 1≤a*b*u := by apply Nat.succ_le_of_lt; positivity
  have hlarge : 2≤12*a*b*u := by nlinarith
  omega

lemma qForm_cast {a b u : ℕ} (ha : 0<a) (hb : 0<b) (hu : 0<u) :
    (qForm a b u:ℝ)=12*(a:ℝ)*(b:ℝ)*(u:ℝ)-1 := by
  have h : 1≤12*a*b*u := by apply Nat.succ_le_of_lt; positivity
  simp only [qForm,Nat.cast_sub h,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]

lemma qForm_cast_int {a b u : ℕ} (ha : 0<a) (hb : 0<b) (hu : 0<u) :
    (qForm a b u:ℤ)=Late.modulus a b u := by
  have h : 1≤12*a*b*u := by apply Nat.succ_le_of_lt; positivity
  simp only [qForm,Late.modulus,Nat.cast_sub h,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]

lemma qForm_encode (a b u : ℕ) : Late.Q (Late.encode (a,b,u))=qForm a b u := by
  dsimp [Late.Q,Late.encode,Late.row,qForm]
  congr 1
  ring

lemma scaleWeight_nonneg (a b u : ℕ) : 0≤scaleWeight a b u := by
  unfold scaleWeight
  positivity

lemma keptScaleWeight_nonneg (a b w u : ℕ) : 0≤keptScaleWeight a b w u := by
  unfold keptScaleWeight
  split_ifs
  · exact scaleWeight_nonneg _ _ _
  · rfl

lemma scaleWeight_le {a b u : ℕ} (ha : 0<a) (hb : 0<b) (hu : 0<u) :
    scaleWeight a b u ≤ 1/(11*(a:ℝ)*(b:ℝ)*(u:ℝ)) := by
  have hprod : (1:ℝ)≤(a:ℝ)*(b:ℝ)*(u:ℝ) := by
    exact_mod_cast (show 1≤a*b*u by apply Nat.succ_le_of_lt; positivity)
  have hden : 11*(a:ℝ)*(b:ℝ)*(u:ℝ)≤(qForm a b u:ℝ) := by
    rw [qForm_cast ha hb hu]
    nlinarith
  exact one_div_le_one_div_of_le (by positivity) hden

lemma sum_Ioc_split (f : ℕ → ℝ) (l m u : ℕ) (hlm : l≤ m) (hmu : m≤u) :
    (∑ x∈Ioc l u,f x)=(∑ x∈Ioc l m,f x)+(∑ x∈Ioc m u,f x) := by
  have heq : Ioc l u=(Ioc l m)∪(Ioc m u) := by
    ext x
    simp only [mem_Ioc,mem_union]
    omega
  have hd : Disjoint (Ioc l m) (Ioc m u) := disjoint_left.mpr (by
    intro x hx hy
    have h1 := (mem_Ioc.mp hx).2
    have h2 := (mem_Ioc.mp hy).1
    omega)
  rw [heq,sum_union hd]

lemma dyadic_Ioc_sum (f : ℕ → ℝ) (U J : ℕ) :
    (∑ u∈Ioc U (2^J*U),f u)=
      ∑ j∈range J, ∑ u∈Ioc (2^j*U) (2^(j+1)*U),f u := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [sum_Ioc_split f U (2^J*U) (2^(J+1)*U),ih,sum_range_succ]
    · exact Nat.le_mul_of_pos_left U (by positivity)
    · apply Nat.mul_le_mul_right U
      exact Nat.pow_le_pow_right (by decide) (Nat.le_succ J)

lemma scale_range_dyadic (n : ℕ) :
    (2:ℕ)^(2*n)*(2^n)^4=(2^n)^6 := by
  rw [← pow_mul,← pow_add,← pow_mul]
  congr 1
  omega

/-- An explicit unit inverse, obtained from one natural progression hit. -/
lemma coprime_of_linear_hit (c q u : ℕ) (hq : 0<q) (hcu : 1≤c*u)
    (h : q∣c*u-1) : Nat.Coprime c q := by
  letI : NeZero q := ⟨hq.ne'⟩
  have heq : (c:ZMod q)*(u:ZMod q)=1 := by
    have hz : ((c*u-1:ℕ):ZMod q)=0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
    simpa only [Nat.cast_sub hcu,Nat.cast_mul,Nat.cast_one,sub_eq_zero] using hz
  have hu : IsUnit (c:ZMod q) := by
    refine ⟨⟨(c:ZMod q),(u:ZMod q),heq,?_⟩,rfl⟩
    simpa [mul_comm] using heq
  rwa [ZMod.isUnit_iff_coprime] at hu

/-- The number of hits in a full natural interval has the same literal upper error. -/
lemma linear_hits_Ioc_le (c d U H : ℕ) (hc : 2≤c) (hd : 0<d) :
    (((Ioc U (U+H)).filter (fun u => d∣c*u-1)).card:ℝ)≤(H:ℝ)/(d:ℝ)+1 := by
  classical
  let s := (Ioc U (U+H)).filter (fun u => d∣c*u-1)
  by_cases hs : s.Nonempty
  · obtain ⟨u,hu⟩ := hs
    have hu0 : 0<u := lt_of_le_of_lt (Nat.zero_le _) (mem_Ioc.mp (mem_filter.mp hu).1).1
    have hcq := coprime_of_linear_hit c d u hd (by apply Nat.succ_le_of_lt; exact Nat.mul_pos (by omega) hu0) (mem_filter.mp hu).2
    have heq : (s.card:ℝ)=∑ i:Fin H, indicator ((c:ZMod d)*((U+1+i.val:ℕ):ZMod d)=1) := by
      have hcard : s.card=(Finset.univ.filter (fun i:Fin H =>
          (c:ZMod d)*((U+1+i.val:ℕ):ZMod d)=1)).card := by
        apply card_bij (fun u hu => (⟨u-(U+1), by
          have := mem_Ioc.mp (mem_filter.mp hu).1
          omega⟩ : Fin H))
        · intro u hu
          have hui := mem_Ioc.mp (mem_filter.mp hu).1
          have he : U+1+(u-(U+1))=u := by omega
          apply mem_filter.mpr
          refine ⟨mem_univ _,?_⟩
          rw [he]
          have hcu : 1≤c*u := Nat.mul_pos (by omega) (by omega)
          have hz := (ZMod.natCast_eq_zero_iff (c*u-1) d).mpr (mem_filter.mp hu).2
          simpa [Nat.cast_sub hcu,sub_eq_zero] using hz
        · intro u hu v hv h
          have he := congrArg (fun i : Fin H => i.val) h
          change u - (U + 1) = v - (U + 1) at he
          have hU := mem_Ioc.mp (mem_filter.mp hu).1
          have hV := mem_Ioc.mp (mem_filter.mp hv).1
          omega
        · intro i hi
          refine ⟨U+1+i.val,?_,?_⟩
          · apply mem_filter.mpr
            refine ⟨mem_Ioc.mpr ⟨by omega,by have := i.isLt; omega⟩,?_⟩
            have hcu : 1≤c*(U+1+i.val) := Nat.mul_pos (by omega) (by omega)
            apply (ZMod.natCast_eq_zero_iff _ d).mp
            simpa [Nat.cast_sub hcu,sub_eq_zero] using (mem_filter.mp hi).2
          · apply Fin.ext
            simp
      rw [hcard]
      simp [indicator,sum_boole]
    rw [heq]
    have he := linear_residue_error c d (U+1) H hd hcq
    linarith [(abs_le.mp he).2]
  · have : s=∅ := not_nonempty_iff_eq_empty.mp hs
    change (s.card:ℝ)≤_
    rw [this]
    simp only [card_empty,Nat.cast_zero]
    positivity

/-- A delayed dyadic scale block: first-hit cost is included in U/d+1. -/
lemma scaleAP_block (a b d U : ℕ) (ha : 0<a) (hb : 0<b)
    (hd : 0<d) (hdU : d≤U) :
    scaleAP a b d U (2*U)≤2/(11*(a:ℝ)*(b:ℝ)*(d:ℝ)) := by
  classical
  have hU : 0<U := hd.trans_le hdU
  let s := (Ioc U (2*U)).filter (fun u => d∣qForm a b u)
  have hsum : scaleAP a b d U (2*U)=∑ u∈s,scaleWeight a b u := by
    rw [scaleAP,←sum_filter]
  have hcount : (s.card:ℝ)≤(U:ℝ)/(d:ℝ)+1 := by
    simpa only [qForm,show U+U=2*U by omega] using
      linear_hits_Ioc_le (12*a*b) d U U (by nlinarith [Nat.mul_pos ha hb]) hd
  have hcount' : (s.card:ℝ)≤2*(U:ℝ)/(d:ℝ) := by
    have hdu : (1:ℝ)≤(U:ℝ)/(d:ℝ) := (le_div_iff₀ (by exact_mod_cast hd)).mpr
      (by simpa using (show (d:ℝ)≤(U:ℝ) by exact_mod_cast hdU))
    calc
      (s.card : ℝ) ≤ (U : ℝ) / (d : ℝ) + 1 := hcount
      _ ≤ (U : ℝ) / (d : ℝ) + (U : ℝ) / (d : ℝ) := add_le_add_right hdu _
      _ = 2 * (U : ℝ) / (d : ℝ) := by ring
  rw [hsum]
  calc
    (∑ u∈s,scaleWeight a b u)≤∑ _u∈s,1/(11*(a:ℝ)*(b:ℝ)*(U:ℝ)) := by
      apply sum_le_sum
      intro u hu
      have huU := (mem_Ioc.mp (mem_filter.mp hu).1).1
      have hu0 : 0<u := hU.trans huU
      exact (scaleWeight_le ha hb hu0).trans (one_div_le_one_div_of_le (by positivity)
        (by gcongr))
    _ = (s.card:ℝ)/(11*(a:ℝ)*(b:ℝ)*(U:ℝ)) := by simp; ring
    _ ≤ (2*(U:ℝ)/(d:ℝ))/(11*(a:ℝ)*(b:ℝ)*(U:ℝ)) := by gcongr
    _ = 2/(11*(a:ℝ)*(b:ℝ)*(d:ℝ)) := by
      have haR : (a:ℝ)≠0 := by positivity
      have hbR : (b:ℝ)≠0 := by positivity
      have hUR : (U:ℝ)≠0 := by positivity
      have hdR : (d:ℝ)≠0 := by positivity
      field_simp <;> ring

/-- Full delayed scale progression. It retains the full modulus d. -/
lemma scaleAP_dyadic (n a b d : ℕ) (ha : 0<a) (hb : 0<b)
    (hd : 0<d) (hdB : d≤(2^n)^4) :
    scaleAP a b d ((2^n)^4) ((2^n)^6)≤
      4*(n:ℝ)/(11*(a:ℝ)*(b:ℝ)*(d:ℝ)) := by
  have heq : scaleAP a b d ((2^n)^4) ((2^n)^6)=
      ∑ j∈range (2*n),scaleAP a b d (2^j*(2^n)^4) (2^(j+1)*(2^n)^4) := by
    rw [scaleAP,←scale_range_dyadic n,dyadic_Ioc_sum]
    rfl
  rw [heq]
  calc
    (∑ j∈range (2*n),scaleAP a b d (2^j*(2^n)^4) (2^(j+1)*(2^n)^4))≤
        ∑ _j∈range (2*n),2/(11*(a:ℝ)*(b:ℝ)*(d:ℝ)) := by
      apply sum_le_sum
      intro j hj
      have hU : d≤2^j*(2^n)^4 := hdB.trans (Nat.le_mul_of_pos_left _ (by positivity))
      simpa only [pow_succ,mul_assoc,mul_left_comm,mul_comm] using
        scaleAP_block a b d (2^j*(2^n)^4) ha hb hd hU
    _ = 4*(n:ℝ)/(11*(a:ℝ)*(b:ℝ)*(d:ℝ)) := by simp; ring

/-- Each complete long dyadic block contributes uniformly to the retained mean. -/
lemma keptScale_block_lower (a b U w : ℕ) (ha : 0<a) (hb : 0<b)
    (hw : 2≤w) (hU : sieveLength w≤U) :
    V w/(48*(a:ℝ)*(b:ℝ))≤∑ u∈Ioc U (2*U),keptScaleWeight a b w u := by
  classical
  have hlen0 : 0<sieveLength w := by dsimp [sieveLength]; positivity
  have hUp : 0<U := hlen0.trans_le hU
  let s := roughScales (12*a*b) U U w
  have hsieve := (sieve_relative (12*a*b) U U w (by nlinarith [Nat.mul_pos ha hb]) hw hU).1
  have hc : (U:ℝ)*V w/2≤(s.card:ℝ) := by
    have hm := mul_le_mul_of_nonneg_left (V_le_Vcoeff (12*a*b) w) (by positivity : (0:ℝ)≤(U:ℝ))
    dsimp [s]
    linarith
  have heq : (∑ u∈Ioc U (2*U),keptScaleWeight a b w u)=∑ u∈s,scaleWeight a b u := by
    simp only [keptScaleWeight,s,roughScales,show U+U=2*U by omega,sum_filter,qForm]
  have hterm : ∀ u∈s,1/(24*(a:ℝ)*(b:ℝ)*(U:ℝ))≤scaleWeight a b u := by
    intro u hu
    have hui := mem_Ioc.mp (mem_filter.mp hu).1
    have hu0 : 0<u := by omega
    have hq0 : (0:ℝ)<(qForm a b u:ℝ) := by exact_mod_cast qForm_pos ha hb hu0
    apply one_div_le_one_div_of_le hq0
    rw [qForm_cast ha hb hu0]
    have huu : (u:ℝ)≤2*(U:ℝ) := by exact_mod_cast (show u ≤ 2 * U by omega)
    nlinarith [mul_le_mul_of_nonneg_left huu (by positivity : (0:ℝ)≤12*(a:ℝ)*(b:ℝ))]
  rw [heq]
  calc
    V w/(48*(a:ℝ)*(b:ℝ))=((U:ℝ)*V w/2)/(24*(a:ℝ)*(b:ℝ)*(U:ℝ)) := by
      have haR : (a:ℝ)≠0 := by positivity
      have hbR : (b:ℝ)≠0 := by positivity
      have hUR : (U:ℝ)≠0 := by positivity
      field_simp <;> ring
    _ ≤ (s.card:ℝ)/(24*(a:ℝ)*(b:ℝ)*(U:ℝ)) := by gcongr
    _ = ∑ _u∈s,1/(24*(a:ℝ)*(b:ℝ)*(U:ℝ)) := by simp; ring
    _ ≤ ∑ u∈s,scaleWeight a b u := sum_le_sum hterm

lemma keptScale_dyadic_lower (n a b w : ℕ) (ha : 0<a) (hb : 0<b)
    (hw : 2≤w) (hlen : sieveLength w≤(2^n)^4) :
    (n:ℝ)*V w/(24*(a:ℝ)*(b:ℝ))≤
      ∑ u∈Ioc ((2^n)^4) ((2^n)^6),keptScaleWeight a b w u := by
  rw [←scale_range_dyadic n,dyadic_Ioc_sum]
  have h : (∑ _j∈range (2*n),V w/(48*(a:ℝ)*(b:ℝ)))≤
      ∑ j∈range (2*n),∑ u∈Ioc (2^j*(2^n)^4) (2^(j+1)*(2^n)^4),keptScaleWeight a b w u := by
    apply sum_le_sum
    intro j hj
    have hU := hlen.trans (Nat.le_mul_of_pos_left ((2^n)^4) (by positivity : 0<2^j))
    simpa only [pow_succ,mul_assoc,mul_left_comm,mul_comm] using
      keptScale_block_lower a b (2^j*(2^n)^4) w ha hb hw hU
  have hleft : (∑ _j∈range (2*n),V w/(48*(a:ℝ)*(b:ℝ))) =
      (n:ℝ)*V w/(24*(a:ℝ)*(b:ℝ)) := by
    simp only [sum_const,card_range,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat]
    have haR : (a:ℝ)≠0 := by positivity
    have hbR : (b:ℝ)≠0 := by positivity
    field_simp
    ring
  rw [hleft] at h
  exact h

/-- Reindex the actual selected packet sum by rays and scales, with no duplicates. -/
lemma mean_eq_ray_scale (B : ℕ) (hB : 2≤B) :
    Late.mean B=∑ r∈raySet (Late.rayCutoff B) B,
      ∑ u∈Ioc (B^4) (B^6),keptScaleWeight r.1 r.2 (Late.cutoff (B^8)) u := by
  classical
  unfold Late.mean Late.packets
  have hinj : Set.InjOn Late.encode (Late.parameters B) := by
    intro t ht t' ht' h
    apply Late.encode_injOn B
    · change t∈(Late.paramBox B).filter (Late.GoodParam B) at ht
      exact (mem_filter.mp ht).2
    · change t'∈(Late.paramBox B).filter (Late.GoodParam B) at ht'
      exact (mem_filter.mp ht').2
    · exact h
  rw [sum_image hinj]
  let rays := raySet (Late.rayCutoff B) B
  let scales := Ioc (B^4) (B^6)
  let s := (rays.product scales).filter (fun z =>
    Late.cutoff (B^8)<Nat.minFac (qForm z.1.1 z.1.2 z.2))
  have heq : (∑ t∈Late.parameters B,1/(Late.Q (Late.encode t):ℝ))=
      ∑ z∈s,scaleWeight z.1.1 z.1.2 z.2 := by
    refine sum_bij (fun t _ => ((t.1,t.2.1),t.2.2)) ?_ ?_ ?_ ?_
    · rintro ⟨a,b,u⟩ ht
      obtain ⟨_,hK,hab,hbB,hcop,huL,huU,hr⟩ := (mem_filter.mp ht).2
      have hK2 : 2≤Late.rayCutoff B := by dsimp [Late.rayCutoff]; omega
      have ha : 1≤a := (by omega : 1≤2).trans (hK2.trans hK)
      have hb : 1≤b := ha.trans hab.le
      have haB : a≤B := hab.le.trans hbB
      apply mem_filter.mpr
      refine ⟨mem_product.mpr ⟨?_,mem_Ioc.mpr ⟨huL,huU⟩⟩,?_⟩
      · exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_pairBox.mpr ⟨ha,haB,hb,hbB⟩,hcop⟩,hK,hab⟩
      · simpa [qForm_encode] using hr
    · rintro ⟨a,b,u⟩ ht ⟨c,e,v⟩ ht' h
      simp only [Prod.mk.injEq] at h ⊢
      tauto
    · rintro ⟨⟨a,b⟩,u⟩ hz
      obtain ⟨hzbox,hr⟩ := mem_filter.mp hz
      obtain ⟨hray,hu⟩ := mem_product.mp hzbox
      obtain ⟨hcbox,hK,hab⟩ := mem_filter.mp hray
      obtain ⟨habox,hcop⟩ := mem_filter.mp hcbox
      have hb := mem_pairBox.mp habox
      refine ⟨(a,b,u),mem_filter.mpr ⟨?_,?_⟩,rfl⟩
      · simp only [Late.paramBox,Finset.product_eq_sprod,mem_product,mem_range]
        exact ⟨by omega,by omega,by have := (mem_Ioc.mp hu).2; omega⟩
      · exact ⟨hB,hK,hab,hb.2.2.2,hcop,(mem_Ioc.mp hu).1,(mem_Ioc.mp hu).2,
          by simpa [qForm_encode] using hr⟩
    · rintro ⟨a,b,u⟩ ht
      simp [scaleWeight,qForm_encode]
  rw [heq]
  dsimp [s]
  rw [sum_filter,sum_product]
  rfl

/-- A larger ray lower cutoff only restricts the witnesses; the mean cannot increase. -/
lemma mean_ge_ray_scale (B K : ℕ) (hB : 2≤B) (hK : Late.rayCutoff B≤K) :
    (∑ r∈raySet K B,∑ u∈Ioc (B^4) (B^6),keptScaleWeight r.1 r.2 (Late.cutoff (B^8)) u)
      ≤ Late.mean B := by
  rw [mean_eq_ray_scale B hB]
  apply sum_le_sum_of_subset_of_nonneg
  · intro r hr
    obtain ⟨hcop,hKr,hlt⟩ := mem_filter.mp hr
    exact mem_filter.mpr ⟨hcop,hK.trans hKr,hlt⟩
  · intro r hr _
    exact sum_nonneg (fun u _ => keptScaleWeight_nonneg _ _ _ _)

/-- The genuinely finite lower-mean theorem. Its only length premise is the explicit sieve length. -/
theorem mean_dyadic_lower_finite (n K : ℕ) (hn : 1≤n)
    (hK : Late.rayCutoff (2^n)≤K)
    (hw : 2≤Late.cutoff ((2^n)^8))
    (hlen : sieveLength (Late.cutoff ((2^n)^8))≤(2^n)^4) :
    (n:ℝ)*V (Late.cutoff ((2^n)^8))*rayMass K (2^n)/24≤Late.mean (2^n) := by
  have hB : 2≤2^n := by simpa using Nat.pow_le_pow_right (by decide : 1≤2) hn
  calc
    (n:ℝ)*V (Late.cutoff ((2^n)^8))*rayMass K (2^n)/24 =
        ∑ r∈raySet K (2^n),(n:ℝ)*V (Late.cutoff ((2^n)^8))/(24*(r.1:ℝ)*(r.2:ℝ)) := by
      unfold rayMass pairWeight
      rw [mul_sum,sum_div]
      apply sum_congr rfl
      intro r hr
      ring
    _ ≤ ∑ r∈raySet K (2^n),∑ u∈Ioc ((2^n)^4) ((2^n)^6),
        keptScaleWeight r.1 r.2 (Late.cutoff ((2^n)^8)) u := by
      apply sum_le_sum
      intro r hr
      have hrbox := mem_pairBox.mp (mem_filter.mp (mem_filter.mp hr).1).1
      exact keptScale_dyadic_lower n r.1 r.2 _ hrbox.1 hrbox.2.2.1 hw hlen
    _ ≤ Late.mean (2^n) := mean_ge_ray_scale _ K hB hK

end
end PrimeAbundance.Analytic
