/- Actual finite family and exact counting conventions.
Uncompiled source. The mean and overlap estimates are NOT proved in this file. -/
import PrimeAbundance.Arithmetic

set_option autoImplicit false
open scoped BigOperators

namespace PrimeAbundance
namespace Late

noncomputable section

abbrev Param := ℕ × ℕ × ℕ
abbrev Packet := ℕ × ℕ

def cutoff (Y : ℕ) : ℕ := ⌊(Real.log (Y : ℝ)) ^ 100⌋₊
def rayCutoff (B : ℕ) : ℕ := ⌊(Real.log (B : ℝ)) ^ 2⌋₊ + 2

def encode (t : Param) : Packet := (row t.1 t.2.1 t.2.2, label t.1 t.2.2)
def Q (p : Packet) : ℕ := 4 * p.1 - 1

def GoodParam (B : ℕ) (t : Param) : Prop :=
  2 ≤ B ∧ rayCutoff B ≤ t.1 ∧ t.1 < t.2.1 ∧ t.2.1 ≤ B ∧
  Nat.Coprime t.1 t.2.1 ∧ B ^ 4 < t.2.2 ∧ t.2.2 ≤ B ^ 6 ∧
  cutoff (B ^ 8) < Nat.minFac (Q (encode t))

def paramBox (B : ℕ) : Finset Param :=
  (Finset.range (B + 1)).product
    ((Finset.range (B + 1)).product (Finset.range (B ^ 6 + 1)))

def parameters (B : ℕ) : Finset Param := by
  classical
  exact (paramBox B).filter (GoodParam B)

def packets (B : ℕ) : Finset Packet := (parameters B).image encode

def Authentic (Y : ℕ) (p : Packet) : Prop :=
  1 ≤ p.1 ∧ p.1 ≤ 3 * Y ∧ 3 ∣ p.1 ∧ 0 < p.2 ∧ p.2 < p.1 ∧
  p.2 ∣ p.1 ^ 2 ∧ cutoff Y < Nat.minFac (Q p)

def mean (B : ℕ) : ℝ := ∑ p ∈ packets B, 1 / (Q p : ℝ)

/-- Unordered distinct ROWS, full gcd, full compatibility. -/
def overlap (B : ℕ) : ℝ := by
  classical
  exact ∑ p ∈ packets B, ∑ p' ∈ packets B,
    if Q p < Q p' ∧ 1 < Nat.gcd (Q p) (Q p') ∧
        Nat.ModEq (Nat.gcd (Q p) (Q p')) p.2 p'.2
    then (Nat.gcd (Q p) (Q p') : ℝ) / ((Q p : ℝ) * (Q p' : ℝ))
    else 0

def firingCount (B n : ℕ) : ℕ :=
  ((packets B).filter fun p => Q p ∣ n + 4 * p.2).card

/-- A selected parameter is a genuine original packet at Y=B^8. -/
theorem encode_authentic (B : ℕ) (t : Param) (ht : GoodParam B t) :
    Authentic (B ^ 8) (encode t) := by
  rcases t with ⟨a, b, u⟩
  rcases ht with ⟨hB, hK, hab, hbB, hcop, huL, huU, hrough⟩
  have ha : 0 < a := by
    have : 2 ≤ rayCutoff B := by dsimp [rayCutoff]; omega
    omega
  have hb : 0 < b := lt_trans ha hab
  have hu : 0 < u := lt_of_le_of_lt (Nat.zero_le _) huL
  have haB : a ≤ B := le_trans (Nat.le_of_lt hab) hbB
  refine ⟨?_, row_le_cutoff B a b u haB hbB huU, row_dvd_three a b u,
    label_pos a u ha hu, label_lt_row a b u ha hu hab,
    label_dvd_row_sq a b u, hrough⟩
  exact row_pos a b u ha hb hu

/-- The map is injective on selected parameter triples, independently of image deduplication. -/
theorem encode_injOn (B : ℕ) : Set.InjOn encode {t : Param | GoodParam B t} := by
  intro t ht t' ht' h
  rcases t with ⟨a, b, u⟩
  rcases t' with ⟨c, e, v⟩
  rcases ht with ⟨hB, hKa, hab, hbB, hcop, huL, huU, hrough⟩
  rcases ht' with ⟨hB', hKc, hce, heB, hcop', hvL, hvU, hrough'⟩
  have hK : 2 ≤ rayCutoff B := by dsimp [rayCutoff]; omega
  have ha : 0 < a := by omega
  have hc : 0 < c := by omega
  have hb : 0 < b := lt_trans ha hab
  have he : 0 < e := lt_trans hc hce
  have hu : 0 < u := lt_of_le_of_lt (Nat.zero_le _) huL
  have hv : 0 < v := lt_of_le_of_lt (Nat.zero_le _) hvL
  have hM : row a b u = row c e v := congrArg Prod.fst h
  have hs : label a u = label c v := congrArg Prod.snd h
  obtain ⟨hac, hbe, huv⟩ := parameter_unique a b c e u v
    ha hb hu hc he hv hcop hcop' hM hs
  subst c
  subst e
  subst v
  rfl

theorem mem_packets_authentic (B : ℕ) (p : Packet) (hp : p ∈ packets B) :
    Authentic (B ^ 8) p := by
  classical
  rcases Finset.mem_image.mp hp with ⟨t, ht, rfl⟩
  exact encode_authentic B t (Finset.mem_filter.mp ht).2

theorem mean_nonneg (B : ℕ) : 0 ≤ mean B := by
  unfold mean
  positivity

theorem overlap_nonneg (B : ℕ) : 0 ≤ overlap B := by
  classical
  unfold overlap
  apply Finset.sum_nonneg
  intro p hp
  apply Finset.sum_nonneg
  intro p' hp'
  split_ifs <;> positivity

end
end Late
end PrimeAbundance
