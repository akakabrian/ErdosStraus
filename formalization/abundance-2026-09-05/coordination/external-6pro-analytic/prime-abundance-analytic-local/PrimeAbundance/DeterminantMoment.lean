/- A harmonic determinant bound obtained from the third divisor moment. -/
import PrimeAbundance.DivisorMoments
import PrimeAbundance.PrimeProduct

set_option autoImplicit false
open scoped Classical
open scoped BigOperators
open Finset

namespace PrimeAbundance.Analytic
noncomputable section

def gap (x y : ℕ) : ℕ := if x≤y then y-x else x-y

lemma gap_comm (x y : ℕ) : gap x y=gap y x := by
  unfold gap
  split_ifs <;> omega

lemma gap_pos {x y : ℕ} (h : x≠y) : 0<gap x y := by
  unfold gap
  split_ifs <;> omega

lemma gap_le_max (x y : ℕ) : gap x y ≤ max x y := by
  unfold gap
  split_ifs <;> omega

lemma gap_cast_int (x y : ℕ) : (gap x y:ℤ)=|(x:ℤ)-(y:ℤ)| := by
  unfold gap
  by_cases h : x≤y
  · rw [if_pos h, Nat.cast_sub h, abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast h))]
    ring
  · rw [if_neg h, Nat.cast_sub (by omega), abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast (by omega : y≤x)))]

lemma nat_dvd_gap_iff (d x y : ℕ) :
    d∣gap x y ↔ (d:ℤ)∣(x:ℤ)-(y:ℤ) := by
  rw [← Int.natCast_dvd_natCast, gap_cast_int, dvd_abs]

/-- For each x there are at most two y with a prescribed unsigned difference. -/
lemma gap_fiber_card_left (s t : Finset ℕ) (d : ℕ) :
    ((s.product t).filter (fun p => gap p.1 p.2=d)).card ≤ 2*s.card := by
  classical
  let F := (s.product t).filter (fun p => gap p.1 p.2=d)
  let f : ℕ × ℕ → ℕ × Bool := fun p => (p.1, decide (p.1≤p.2))
  have hf : Set.InjOn f F := by
    rintro ⟨x,y⟩ hp ⟨x',y'⟩ hq h
    have hx : x=x' := congrArg Prod.fst h
    have hs : decide (x≤y)=decide (x'≤y') := congrArg Prod.snd h
    have hg : gap x y=gap x' y' :=
      (mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm
    subst x'
    have hy : y=y' := by
      by_cases hxy : x≤y <;> by_cases hxy' : x≤y' <;>
        simp only [hxy,hxy',decide_true,decide_false,Bool.false_eq_true,
          Bool.true_eq_false] at hs
      all_goals simp only [gap,hxy,hxy',if_true,if_false] at hg
      all_goals omega
    subst y'
    rfl
  have hmap : F.image f ⊆ s.product (univ : Finset Bool) := by
    intro z hz
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hz
    exact mem_product.mpr ⟨(mem_product.mp (mem_filter.mp hp).1).1,mem_univ _⟩
  calc
    F.card=(F.image f).card := (card_image_of_injOn hf).symm
    _ ≤ (s.product (univ : Finset Bool)).card := card_le_card hmap
    _ = 2*s.card := by simp; ring

lemma gap_fiber_card_right (s t : Finset ℕ) (d : ℕ) :
    ((s.product t).filter (fun p => gap p.1 p.2=d)).card ≤ 2*t.card := by
  classical
  let F := (s.product t).filter (fun p => gap p.1 p.2=d)
  let G := (t.product s).filter (fun p => gap p.1 p.2=d)
  have heq : F.image Prod.swap=G := by
    ext p
    rcases p with ⟨x,y⟩
    simp only [F,G,mem_image,mem_filter,Finset.product_eq_sprod,mem_product,Prod.exists,Prod.swap_prod_mk,
      Prod.mk.injEq]
    constructor
    · rintro ⟨a,b,⟨hab,hgap⟩,rfl,rfl⟩
      exact ⟨⟨hab.2,hab.1⟩,by simpa [gap_comm] using hgap⟩
    · rintro ⟨⟨hx,hy⟩,hgap⟩
      exact ⟨y,x,⟨⟨hy,hx⟩,by simpa [gap_comm] using hgap⟩,rfl,rfl⟩
  have hinj : Set.InjOn (Prod.swap : ℕ × ℕ → ℕ × ℕ) (F : Set (ℕ × ℕ)) := by
    intro p hp q hq h
    have h' := congrArg Prod.swap h
    simpa using h'
  have hcard : F.card=G.card := by rw [← heq,card_image_of_injOn hinj]
  rw [hcard]
  exact gap_fiber_card_left t s d

def offDiagonal (s t : Finset ℕ) : Finset (ℕ × ℕ) :=
  (s.product t).filter (fun p => p.1≠p.2)

lemma gap_cube_rectangle (i j X : ℕ) (hi : 2^i≤X) (hj : 2^j≤X) :
    (∑ p∈offDiagonal (dyadicBlock i) (dyadicBlock j), (tau (gap p.1 p.2):ℝ)^3) ≤
      4*((2^i:ℕ):ℝ)*((2^j:ℕ):ℝ)*(1+Real.log ((2*X:ℕ):ℝ))^7 := by
  let U := 2^i
  let W := 2^j
  let Z := 2*max U W
  let s := offDiagonal (dyadicBlock i) (dyadicBlock j)
  have hU : 0<U := by dsimp [U]; positivity
  have hW : 0<W := by dsimp [W]; positivity
  have hZ : 0<Z := by dsimp [Z]; positivity
  have hmap : ∀ p∈s, gap p.1 p.2∈Icc 1 Z := by
    intro p hp
    obtain ⟨hpbox,hne⟩ := mem_filter.mp hp
    obtain ⟨hpx,hpy⟩ := mem_product.mp hpbox
    have hx := (mem_Ico.mp hpx).2
    have hy := (mem_Ico.mp hpy).2
    rw [pow_succ] at hx hy
    refine mem_Icc.mpr ⟨gap_pos hne, ?_⟩
    dsimp [Z,U,W] at *
    have := gap_le_max p.1 p.2
    omega
  have hfib : ∀ d∈Icc 1 Z, (s.filter (fun p => gap p.1 p.2=d)).card ≤ 2*min U W := by
    intro d hd
    have hsub : s.filter (fun p => gap p.1 p.2=d) ⊆
        ((dyadicBlock i).product (dyadicBlock j)).filter (fun p => gap p.1 p.2=d) := by
      intro p hp
      obtain ⟨hs,hg⟩ := mem_filter.mp hp
      exact mem_filter.mpr ⟨(mem_filter.mp hs).1,hg⟩
    have hleft := (card_le_card hsub).trans (gap_fiber_card_left (dyadicBlock i) (dyadicBlock j) d)
    have hright := (card_le_card hsub).trans (gap_fiber_card_right (dyadicBlock i) (dyadicBlock j) d)
    rw [dyadicBlock_card] at hleft hright
    by_cases h : U≤W
    · simpa only [min_eq_left h] using hleft
    · simpa only [min_eq_right (le_of_not_ge h)] using hright
  have hsum := sum_le_mul_sum_of_fiber_bound s (Icc 1 Z)
    (fun p => gap p.1 p.2) (fun d => (tau d:ℝ)^3) (2*min U W)
    hmap hfib (fun d _ => by positivity)
  have hprefix := tau_cube_prefix Z
  have hZX : Z≤2*X := by
    dsimp [Z,U,W]
    exact Nat.mul_le_mul_left 2 (max_le hi hj)
  have hlog : 1+Real.log (Z:ℝ)≤1+Real.log ((2*X:ℕ):ℝ) := by
    have hl : Real.log (Z:ℝ)≤Real.log ((2*X:ℕ):ℝ) := by
      apply Real.log_le_log
      · exact_mod_cast hZ
      · exact_mod_cast hZX
    linarith
  have hp0 : 0≤1+Real.log (Z:ℝ) := by
    have hz1 : (1:ℝ)≤(Z:ℝ) := by exact_mod_cast hZ
    linarith [Real.log_nonneg hz1]
  have hp7 := pow_le_pow_left₀ hp0 hlog 7
  have hprod : (2*min U W:ℕ)*Z=4*U*W := by
    dsimp [Z]
    by_cases h : U≤W
    · rw [min_eq_left h, max_eq_right h]
      ring
    · have h' : W≤U := le_of_not_ge h
      rw [min_eq_right h', max_eq_left h']
      ring
  calc
    (∑ p∈s, (tau (gap p.1 p.2):ℝ)^3)
        ≤ ((2*min U W:ℕ):ℝ)*(∑ d∈Icc 1 Z, (tau d:ℝ)^3) := hsum
    _ ≤ ((2*min U W:ℕ):ℝ)*((Z:ℝ)*(1+Real.log (Z:ℝ))^7) := by gcongr
    _ ≤ ((2*min U W:ℕ):ℝ)*((Z:ℝ)*(1+Real.log ((2*X:ℕ):ℝ))^7) := by gcongr
    _ = 4*((2^i:ℕ):ℝ)*((2^j:ℕ):ℝ)*(1+Real.log ((2*X:ℕ):ℝ))^7 := by
      rw [← mul_assoc,←Nat.cast_mul,hprod]
      simp only [U, W, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

lemma first_cube_rectangle (i j X : ℕ) (hi : 2^i≤X) :
    (∑ p∈offDiagonal (dyadicBlock i) (dyadicBlock j), (tau p.1:ℝ)^3) ≤
      2*((2^i:ℕ):ℝ)*((2^j:ℕ):ℝ)*(1+Real.log ((2*X:ℕ):ℝ))^7 := by
  have hsum : (∑ p∈offDiagonal (dyadicBlock i) (dyadicBlock j), (tau p.1:ℝ)^3) ≤
      ∑ p∈(dyadicBlock i).product (dyadicBlock j), (tau p.1:ℝ)^3 :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun p _ _ => by positivity)
  have hblock : (∑ x∈dyadicBlock i, (tau x:ℝ)^3) ≤
      ((2*2^i:ℕ):ℝ)*(1+Real.log ((2*X:ℕ):ℝ))^7 := by
    have hsub : dyadicBlock i ⊆ Icc 1 (2*2^i) := by
      intro x hx
      obtain ⟨hlo,hhi⟩ := mem_Ico.mp hx
      rw [pow_succ] at hhi
      have hpos : 0<2^i := by positivity
      exact mem_Icc.mpr ⟨by omega,by omega⟩
    have hs := sum_le_sum_of_subset_of_nonneg hsub
      (fun x _ _ => (by positivity : (0:ℝ)≤(tau x:ℝ)^3))
    have hp := tau_cube_prefix (2*2^i)
    have hlog : 1+Real.log ((2*2^i:ℕ):ℝ)≤1+Real.log ((2*X:ℕ):ℝ) := by
      have hl : Real.log ((2*2^i:ℕ):ℝ)≤Real.log ((2*X:ℕ):ℝ) := by
        apply Real.log_le_log
        · positivity
        · exact_mod_cast Nat.mul_le_mul_left 2 hi
      linarith
    have hbase : 0≤1+Real.log ((2*2^i:ℕ):ℝ) := by
      have h1 : (1:ℝ)≤((2*2^i:ℕ):ℝ) := by exact_mod_cast (by apply Nat.succ_le_of_lt; positivity : 1≤2*2^i)
      linarith [Real.log_nonneg h1]
    exact hs.trans (hp.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbase hlog 7) (by positivity)))
  rw [Finset.product_eq_sprod, sum_product] at hsum
  simp only [sum_const,nsmul_eq_mul,dyadicBlock_card] at hsum
  have heq : (∑ x∈dyadicBlock i, ((2^j:ℕ):ℝ)*(tau x:ℝ)^3) =
      ((2^j:ℕ):ℝ)*(∑ x∈dyadicBlock i,(tau x:ℝ)^3) := by rw [mul_sum]
  rw [heq] at hsum
  have hm := mul_le_mul_of_nonneg_left hblock (by positivity : (0:ℝ)≤((2^j:ℕ):ℝ))
  exact hsum.trans (by simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc, mul_comm, mul_left_comm] using hm)

lemma second_cube_rectangle (i j X : ℕ) (hj : 2^j≤X) :
    (∑ p∈offDiagonal (dyadicBlock i) (dyadicBlock j), (tau p.2:ℝ)^3) ≤
      2*((2^i:ℕ):ℝ)*((2^j:ℕ):ℝ)*(1+Real.log ((2*X:ℕ):ℝ))^7 := by
  have heq : (∑ p∈offDiagonal (dyadicBlock i) (dyadicBlock j),(tau p.2:ℝ)^3) =
      ∑ p∈offDiagonal (dyadicBlock j) (dyadicBlock i),(tau p.1:ℝ)^3 := by
    refine sum_bij (fun p _ => p.swap) ?_ ?_ ?_ ?_
    · intro p hp
      obtain ⟨hbox,hne⟩ := mem_filter.mp hp
      obtain ⟨hx,hy⟩ := mem_product.mp hbox
      exact mem_filter.mpr ⟨mem_product.mpr ⟨hy,hx⟩,hne.symm⟩
    · intro p hp q hq h
      have h' := congrArg Prod.swap h
      simpa using h'
    · intro p hp
      refine ⟨p.swap, ?_, by simp⟩
      obtain ⟨hbox,hne⟩ := mem_filter.mp hp
      obtain ⟨hx,hy⟩ := mem_product.mp hbox
      exact mem_filter.mpr ⟨mem_product.mpr ⟨hy,hx⟩,hne.symm⟩
    · intro p hp
      rfl
  rw [heq]
  simpa [mul_comm,mul_left_comm,mul_assoc] using first_cube_rectangle j i X hj

def energyWeight (p : ℕ × ℕ) : ℝ :=
  if p.1=p.2 then 0 else (tau p.1:ℝ)*(tau p.2:ℝ)*(tau (gap p.1 p.2):ℝ)/
    ((p.1:ℝ)*(p.2:ℝ))

def determinantEnergy (X : ℕ) : ℝ :=
  ∑ p∈(Icc 1 X).product (Icc 1 X), energyWeight p

lemma energyWeight_nonneg (p : ℕ × ℕ) : 0≤energyWeight p := by
  unfold energyWeight
  split_ifs <;> positivity

lemma energy_rectangle (i j X : ℕ) (hi : 2^i≤X) (hj : 2^j≤X) :
    (∑ p∈(dyadicBlock i).product (dyadicBlock j), energyWeight p) ≤
      4*(1+Real.log ((2*X:ℕ):ℝ))^7 := by
  let s := offDiagonal (dyadicBlock i) (dyadicBlock j)
  let A : ℝ := 1+Real.log ((2*X:ℕ):ℝ)
  let U : ℝ := ((2^i:ℕ):ℝ)
  let W : ℝ := ((2^j:ℕ):ℝ)
  have hU : 0<U := by dsimp [U]; positivity
  have hW : 0<W := by dsimp [W]; positivity
  have hA : 0≤A := by
    have hX : 1≤X := (show 1≤2^i by apply Nat.succ_le_of_lt; positivity).trans hi
    have h1 : (1:ℝ)≤((2*X:ℕ):ℝ) := by exact_mod_cast (by omega : 1≤2*X)
    dsimp [A]
    linarith [Real.log_nonneg h1]
  have h1 := first_cube_rectangle i j X hi
  have h2 := second_cube_rectangle i j X hj
  have h3 := gap_cube_rectangle i j X hi hj
  have ham := sum_three_mul_le_cubes s
    (fun p => (tau p.1:ℝ)) (fun p => (tau p.2:ℝ))
    (fun p => (tau (gap p.1 p.2):ℝ))
    (fun _ _ => by positivity) (fun _ _ => by positivity) (fun _ _ => by positivity)
  have hprod : (∑ p∈s,(tau p.1:ℝ)*(tau p.2:ℝ)*(tau (gap p.1 p.2):ℝ))≤4*U*W*A^7 := by
    have hnonneg : 0≤U*W*A^7 := by positivity
    change _ ≤ 2*U*W*A^7 at h1 h2
    change _ ≤ 4*U*W*A^7 at h3
    nlinarith
  have heq : (∑ p∈(dyadicBlock i).product (dyadicBlock j),energyWeight p) =
      ∑ p∈s,(tau p.1:ℝ)*(tau p.2:ℝ)*(tau (gap p.1 p.2):ℝ)/((p.1:ℝ)*(p.2:ℝ)) := by
    dsimp only [s,offDiagonal]
    rw [sum_filter]
    apply sum_congr rfl
    intro p hp
    by_cases h : p.1=p.2 <;> simp [energyWeight,h]
  rw [heq]
  calc
    (∑ p∈s,(tau p.1:ℝ)*(tau p.2:ℝ)*(tau (gap p.1 p.2):ℝ)/((p.1:ℝ)*(p.2:ℝ))) ≤
        (∑ p∈s,(tau p.1:ℝ)*(tau p.2:ℝ)*(tau (gap p.1 p.2):ℝ))/(U*W) := by
      rw [sum_div]
      apply sum_le_sum
      intro p hp
      have hb := mem_product.mp (mem_filter.mp hp).1
      have hx : U≤(p.1:ℝ) := by dsimp [U]; exact_mod_cast (mem_Ico.mp hb.1).1
      have hy : W≤(p.2:ℝ) := by dsimp [W]; exact_mod_cast (mem_Ico.mp hb.2).1
      have hden : U*W≤(p.1:ℝ)*(p.2:ℝ) := mul_le_mul hx hy hW.le (hU.le.trans hx)
      exact div_le_div_of_nonneg_left (by positivity) (mul_pos hU hW) hden
    _ ≤ (4*U*W*A^7)/(U*W) := div_le_div_of_nonneg_right hprod (mul_pos hU hW).le
    _ = 4*A^7 := by field_simp <;> ring

/-- The harmonic determinant moment is polylogarithmic without an AP divisor theorem. -/
theorem determinantEnergy_bound (X : ℕ) (hX : 0<X) :
    determinantEnergy X ≤
      4*((Nat.log 2 X+1:ℕ):ℝ)^2*(1+Real.log ((2*X:ℕ):ℝ))^7 := by
  let J := Nat.log 2 X+1
  let indices := (range J).product (range J)
  let boxes : ℕ × ℕ → Finset (ℕ × ℕ) := fun ij =>
    (dyadicBlock ij.1).product (dyadicBlock ij.2)
  have hcover : ∀ p∈(Icc 1 X).product (Icc 1 X),
      ∃ ij∈indices, p∈boxes ij := by
    intro p hp
    obtain ⟨hx,hy⟩ := mem_product.mp hp
    have hx' := mem_Icc.mp hx
    have hy' := mem_Icc.mp hy
    refine ⟨(Nat.log 2 p.1,Nat.log 2 p.2), ?_, ?_⟩
    · apply mem_product.mpr
      constructor <;> apply mem_range.mpr
      · exact Nat.lt_succ_of_le (Nat.log_monotone (b := 2) hx'.2)
      · exact Nat.lt_succ_of_le (Nat.log_monotone (b := 2) hy'.2)
    · exact mem_product.mpr ⟨mem_dyadicBlock_log hx'.1,mem_dyadicBlock_log hy'.1⟩
  have hbox : ∀ ij∈indices,
      (∑ p∈boxes ij,energyWeight p)≤4*(1+Real.log ((2*X:ℕ):ℝ))^7 := by
    intro ij hij
    obtain ⟨hi,hj⟩ := mem_product.mp hij
    exact energy_rectangle ij.1 ij.2 X
      (Nat.pow_le_of_le_log hX.ne' (by have := mem_range.mp hi; dsimp [J] at this; omega))
      (Nat.pow_le_of_le_log hX.ne' (by have := mem_range.mp hj; dsimp [J] at this; omega))
  calc
    determinantEnergy X ≤ ∑ ij∈indices, ∑ p∈boxes ij,energyWeight p :=
      sum_le_sum_of_cover _ _ _ _ energyWeight_nonneg hcover
    _ ≤ ∑ _ij∈indices,4*(1+Real.log ((2*X:ℕ):ℝ))^7 := sum_le_sum hbox
    _ = 4*((Nat.log 2 X+1:ℕ):ℝ)^2*(1+Real.log ((2*X:ℕ):ℝ))^7 := by
      simp [indices,J,pow_two]
      ring

lemma determinantEnergy_dyadic (n : ℕ) :
    determinantEnergy (2^(2*n))≤4096*((n+1:ℕ):ℝ)^9 := by
  have h := determinantEnergy_bound (2^(2*n)) (by positivity)
  rw [Nat.log_pow (by decide)] at h
  have hlog : Real.log ((2*2^(2*n):ℕ):ℝ)=((2*n+1:ℕ):ℝ)*Real.log 2 := by
    rw [show 2*2^(2*n)=2^(2*n+1) by rw [pow_succ]; ring,
      Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
  rw [hlog] at h
  have hn : (0:ℝ)≤(n:ℝ) := by positivity
  have hA0 : 0≤1+((2*n+1:ℕ):ℝ)*Real.log 2 := by (have := log_two_pos; positivity)
  have hA : 1+((2*n+1:ℕ):ℝ)*Real.log 2 ≤ 2*((n+1:ℕ):ℝ) := by
    push_cast
    nlinarith [log_two_lt_one]
  have hJ : ((2*n+1:ℕ):ℝ)≤2*((n+1:ℕ):ℝ) := by push_cast; linarith
  have hbound : 4*((2*n+1:ℕ):ℝ)^2*(1+((2*n+1:ℕ):ℝ)*Real.log 2)^7 ≤
      4*(2*((n+1:ℕ):ℝ))^2*(2*((n+1:ℕ):ℝ))^7 := by gcongr
  have hpoly : 4*(2*((n+1:ℕ):ℝ))^2*(2*((n+1:ℕ):ℝ))^7 =
      2048*((n+1:ℕ):ℝ)^9 := by ring
  rw [hpoly] at hbound
  have hp : 0≤((n+1:ℕ):ℝ)^9 := by positivity
  nlinarith

end
end PrimeAbundance.Analytic
