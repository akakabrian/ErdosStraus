/- Strict Type-II decoding and injective counting for the concrete selected family. -/
import PrimeAbundance.Target
import PrimeAbundance.ScaleSums

set_option autoImplicit false
open scoped Classical
open scoped BigOperators
open Finset

namespace PrimeAbundance
noncomputable section

namespace Late

lemma authentic_Q_add_one {Y : ℕ} {p : Packet} (hp : Authentic Y p) : Q p+1=4*p.1 := by
  have hM := hp.1
  unfold Q
  omega

lemma authentic_Q_pos {Y : ℕ} {p : Packet} (hp : Authentic Y p) : 0<Q p := by
  have hM := hp.1
  have hQ := authentic_Q_add_one hp
  omega

lemma authentic_Q_lt {Y : ℕ} {p : Packet} (hp : Authentic Y p) : Q p<12*Y := by
  have hM := hp.2.1
  have hQ := authentic_Q_add_one hp
  omega

lemma authentic_Q_odd {Y : ℕ} {p : Packet} (hp : Authentic Y p) : Odd (Q p) := by
  have hQ := authentic_Q_add_one hp
  have hM := hp.1
  refine ⟨2*p.1-1,?_⟩
  omega

lemma authentic_coprime {Y : ℕ} {p : Packet} (hp : Authentic Y p) :
    Nat.Coprime p.1 (Q p) ∧ Nat.Coprime p.2 (Q p) := by
  have hM := hp.1
  have hs := hp.2.2.2.2.2.1
  have hQ := authentic_Q_pos hp
  have hmq : Nat.Coprime p.1 (Q p) := by
    apply Analytic.coprime_of_linear_hit p.1 (Q p) 4 hQ (by nlinarith)
    have heq : p.1*4-1=Q p := by unfold Q; congr 1; ring
    rw [heq]
  exact ⟨hmq,Nat.Coprime.of_dvd_left hs (hmq.pow_left 2)⟩

/-- Construction plus recovery equations. The divisibility s | M*x is explicit. -/
theorem exists_decoded {Y n : ℕ} (p : Packet) (hp : Authentic Y p)
    (hfire : Q p∣n+4*p.2) (hn : Q p<n) :
    ∃ t : StrictTriple n,
      t.y=n*p.1 ∧ Q p*t.x=n*p.1+p.2 ∧ n∣t.y ∧ n∣t.z ∧
      (Nat.Prime n → Nat.Coprime n t.x) := by
  rcases p with ⟨M,s⟩
  have hM : 0<M := hp.1
  have hs : 0<s := hp.2.2.2.1
  have hsM : s<M := hp.2.2.2.2.1
  have hsdiv : s∣M^2 := hp.2.2.2.2.2.1
  let q := Q (M,s)
  have hq : 0<q := authentic_Q_pos hp
  have hqeq : q+1=4*M := authentic_Q_add_one hp
  have hn0 : 0<n := hq.trans hn
  have hcop : Nat.Coprime s q := (authentic_coprime hp).2
  have hnum : q∣n*M+s := by
    have h1 : q∣M*(n+4*s) := dvd_mul_of_dvd_right hfire M
    have h2 : q∣q*s := dvd_mul_right q s
    have hid : M*(n+4*s)=(n*M+s)+q*s := by
      calc
        M*(n+4*s)=n*M+(4*M)*s := by ring
        _ = n*M+(q+1)*s := by rw [hqeq]
        _ = (n*M+s)+q*s := by ring
    rw [hid] at h1
    have h := Nat.dvd_sub h1 h2
    simpa only [Nat.add_sub_cancel_right] using h
  let x := (n*M+s)/q
  have hqx : q*x=n*M+s := Nat.mul_div_cancel' hnum
  have hsMx : s∣M*x := by
    have h1 : s∣n*M^2 := dvd_mul_of_dvd_right hsdiv n
    have h2 : s∣M*s := dvd_mul_left s M
    have hid : n*M^2+M*s=q*(M*x) := by
      calc
        n*M^2+M*s=M*(n*M+s) := by ring
        _ = M*(q*x) := by rw [hqx]
        _ = q*(M*x) := by ring
    have h := dvd_add h1 h2
    rw [hid] at h
    exact hcop.dvd_of_dvd_mul_left h
  let t := M*x/s
  have hst : s*t=M*x := Nat.mul_div_cancel' hsMx
  have hxM : M<x := by
    by_contra h
    have hxm : x≤M := Nat.le_of_not_gt h
    have hmul := Nat.mul_le_mul_left q hxm
    have hnm := Nat.mul_lt_mul_of_pos_right hn hM
    nlinarith [hqx]
  have hxs : s<x := hsM.trans hxM
  have hx0 : 0<x := hM.trans hxM
  have hxN : x<n := by
    have hqM : M+1≤q := by omega
    have hnS : s<n := by omega
    have hmulN := Nat.mul_le_mul_left n hqM
    by_contra h
    have hnx : n≤x := Nat.le_of_not_gt h
    have hmulX := Nat.mul_le_mul_left q hnx
    nlinarith [hqx]
  have htM : M<t := by
    by_contra h
    have htm : t≤M := Nat.le_of_not_gt h
    have hmulT := Nat.mul_le_mul_left s htm
    have hmulX := Nat.mul_lt_mul_of_pos_left hxs hM
    nlinarith [hst]
  have ht0 : 0<t := hM.trans htM
  have hxy : x<n*M := hxN.trans_le (Nat.le_mul_of_pos_right n hM)
  have hyz : n*M<n*t := Nat.mul_lt_mul_of_pos_left htM hn0
  have hmain : 4*M*x=n*M+x+s := by
    calc
      4*M*x=(q+1)*x := by rw [hqeq]
      _ = q*x+x := by ring
      _ = n*M+x+s := by rw [hqx]; ring
  have hegypt : (4:ℚ)/(n:ℚ)=1/(x:ℚ)+1/((n*M:ℕ):ℚ)+1/((n*t:ℕ):ℚ) := by
    have hnR : (n:ℚ)≠0 := by positivity
    have hMR : (M:ℚ)≠0 := by positivity
    have hsR : (s:ℚ)≠0 := by positivity
    have hxR : (x:ℚ)≠0 := by positivity
    have htR : (t:ℚ)≠0 := by positivity
    have hstR : (s:ℚ)*(t:ℚ)=(M:ℚ)*(x:ℚ) := by exact_mod_cast hst
    have hmainR : 4*(M:ℚ)*(x:ℚ)=(n:ℚ)*(M:ℚ)+(x:ℚ)+(s:ℚ) := by exact_mod_cast hmain
    have hlast : (1:ℚ)/((n*t:ℕ):ℚ)=(s:ℚ)/((n:ℚ)*(M:ℚ)*(x:ℚ)) := by
      push_cast
      apply (div_eq_div_iff (by positivity) (by positivity)).mpr
      have hm := congrArg (fun z:ℚ => (n:ℚ)*z) hstR
      nlinarith
    rw [hlast,Nat.cast_mul]
    field_simp
    nlinarith [hmainR]
  let out : StrictTriple n := {
    x := x, y := n*M, z := n*t,
    x_pos := hx0, y_pos := Nat.mul_pos hn0 hM, z_pos := Nat.mul_pos hn0 ht0,
    xy := hxy, yz := hyz, egypt := hegypt }
  refine ⟨out,rfl,hqx,dvd_mul_right n M,dvd_mul_right n t,?_⟩
  intro hprime
  apply hprime.coprime_iff_not_dvd.mpr
  intro hnx
  have hle := Nat.le_of_dvd hx0 hnx
  omega

def decoded {Y n : ℕ} (p : Packet) (hp : Authentic Y p)
    (hfire : Q p∣n+4*p.2) (hn : Q p<n) : StrictTriple n :=
  Classical.choose (exists_decoded p hp hfire hn)

lemma decoded_spec {Y n : ℕ} (p : Packet) (hp : Authentic Y p)
    (hfire : Q p∣n+4*p.2) (hn : Q p<n) :
    (decoded p hp hfire hn).y=n*p.1 ∧
    Q p*(decoded p hp hfire hn).x=n*p.1+p.2 ∧
    n∣(decoded p hp hfire hn).y ∧ n∣(decoded p hp hfire hn).z ∧
    (Nat.Prime n→Nat.Coprime n (decoded p hp hfire hn).x) :=
  Classical.choose_spec (exists_decoded p hp hfire hn)

/-- Equality of output triples recovers the packet, not just its ray. -/
lemma decoded_injective {Y n : ℕ} {p q : Packet} (hp : Authentic Y p) (hq : Authentic Y q)
    (hfp : Q p∣n+4*p.2) (hfq : Q q∣n+4*q.2) (hnp : Q p<n) (hnq : Q q<n)
    (heq : decoded p hp hfp hnp=decoded q hq hfq hnq) : p=q := by
  have hn0 : 0<n := (authentic_Q_pos hp).trans hnp
  have hsp := decoded_spec p hp hfp hnp
  have hsq := decoded_spec q hq hfq hnq
  have hy := congrArg StrictTriple.y heq
  have hx := congrArg StrictTriple.x heq
  have hM : p.1=q.1 := by rw [hsp.1,hsq.1] at hy; nlinarith
  have hQ : Q p=Q q := by simp only [Q,hM]
  have hlabel : p.2=q.2 := by
    have hp' := hsp.2.1
    have hq' := hsq.2.1
    rw [hM,hQ,hx] at hp'
    omega
  exact Prod.ext hM hlabel

def firingPackets (B n : ℕ) : Finset Packet :=
  (packets B).filter (fun p => Q p∣n+4*p.2)

lemma firingPackets_card (B n : ℕ) : (firingPackets B n).card=firingCount B n := rfl

/-- Restrict the packet injection to Fin r. No finiteness of the whole solution type is assumed. -/
theorem hasAtLeast_of_firingCount (B n r : ℕ) (hn : Nat.Prime n)
    (hlarge : 12*B^8<n) (hr : r≤firingCount B n) : HasAtLeastTypeIISolutions n r := by
  classical
  let S := firingPackets B n
  let decodeS : S → StrictTriple n := fun p =>
    decoded p.val (mem_packets_authentic B p.val (mem_filter.mp p.property).1)
      (mem_filter.mp p.property).2
      ((authentic_Q_lt (mem_packets_authentic B p.val (mem_filter.mp p.property).1)).trans hlarge)
  have hdinj : Function.Injective decodeS := by
    intro p q h
    apply Subtype.ext
    exact decoded_injective
      (mem_packets_authentic B p.val (mem_filter.mp p.property).1)
      (mem_packets_authentic B q.val (mem_filter.mp q.property).1)
      (mem_filter.mp p.property).2 (mem_filter.mp q.property).2
      ((authentic_Q_lt (mem_packets_authentic B p.val (mem_filter.mp p.property).1)).trans hlarge)
      ((authentic_Q_lt (mem_packets_authentic B q.val (mem_filter.mp q.property).1)).trans hlarge) h
  let e : S ≃ Fin S.card := by simpa using Fintype.equivFin S
  let index : Fin r → Fin S.card := fun i => ⟨i.val, i.isLt.trans_le hr⟩
  have hiinj : Function.Injective index := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun k : Fin S.card => k.val) h
  refine ⟨fun i => decodeS (e.symm (index i)),hdinj.comp (e.symm.injective.comp hiinj),?_⟩
  intro i
  let p := e.symm (index i)
  have hspec := decoded_spec p.val
    (mem_packets_authentic B p.val (mem_filter.mp p.property).1)
    (mem_filter.mp p.property).2
    ((authentic_Q_lt (mem_packets_authentic B p.val (mem_filter.mp p.property).1)).trans hlarge)
  exact ⟨hspec.2.2.1,hspec.2.2.2.1,(hspec.2.2.2.2 hn).gcd_eq_one⟩

end Late
end
end PrimeAbundance
