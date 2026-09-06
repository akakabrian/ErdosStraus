/-
Proof-source candidates for the new arithmetic, not compiled in this environment.
No analytic estimate is assumed here. All variables are explicitly quantified.
The modulus is an integer polynomial, so subtraction is not truncated.
-/
import Mathlib

set_option autoImplicit false

namespace PrimeAbundance
namespace Late

abbrev row (a b u : ℕ) : ℕ := 3 * a * b * u
abbrev label (a u : ℕ) : ℕ := 3 * a ^ 2 * u
abbrev modulus (a b u : ℤ) : ℤ := 12 * a * b * u - 1
abbrev intLabel (a u : ℤ) : ℤ := 3 * a ^ 2 * u
abbrev determinant (a b c e : ℤ) : ℤ := a * e - c * b

/-- The exact full-modulus identity used in the replacement proof. -/
theorem determinant_identity (a b c e u v : ℤ) :
    4 * b * e * (intLabel a u - intLabel c v) =
      a * e * modulus a b u - c * b * modulus c e v + determinant a b c e := by
  dsimp [intLabel, modulus, determinant]
  ring

/-- An explicit inverse for 4*b*e modulo every common divisor of the row moduli.
This avoids a hidden squarefree restriction or a separate coprimality premise. -/
theorem inverse_identity (a b c e u v : ℤ) :
    (4 * b * e) * (36 * a * c * u * v) - 1 =
      modulus a b u * modulus c e v + modulus a b u + modulus c e v := by
  dsimp [modulus]
  ring

/-- Full-modulus compatibility, valid for ANY common integer divisor.
In particular d need not be prime, squarefree, or a radical. -/
theorem full_modulus_compatibility (a b c e u v d : ℤ)
    (hd : d ∣ modulus a b u) (hd' : d ∣ modulus c e v) :
    d ∣ intLabel a u - intLabel c v ↔ d ∣ determinant a b c e := by
  constructor
  · intro hs
    have h₁ : d ∣ 4 * b * e * (intLabel a u - intLabel c v) :=
      dvd_mul_of_dvd_right hs _
    have h₂ : d ∣ a * e * modulus a b u := dvd_mul_of_dvd_right hd _
    have h₃ : d ∣ c * b * modulus c e v := dvd_mul_of_dvd_right hd' _
    have h := dvd_add (dvd_sub h₁ h₂) h₃
    have hid : 4 * b * e * (intLabel a u - intLabel c v) -
        a * e * modulus a b u + c * b * modulus c e v =
        determinant a b c e := by
      rw [determinant_identity]
      ring
    rwa [hid] at h
  · intro hD
    have h₁ : d ∣ a * e * modulus a b u := dvd_mul_of_dvd_right hd _
    have h₂ : d ∣ c * b * modulus c e v := dvd_mul_of_dvd_right hd' _
    have hz : d ∣ 4 * b * e * (intLabel a u - intLabel c v) := by
      rw [determinant_identity]
      exact dvd_add (dvd_sub h₁ h₂) hD
    have hinv : d ∣ (4 * b * e) * (36 * a * c * u * v) - 1 := by
      rw [inverse_identity]
      exact dvd_add (dvd_add (dvd_mul_of_dvd_left hd _) hd) hd'
    have h := dvd_sub
      (dvd_mul_of_dvd_left hz (36 * a * c * u * v))
      (dvd_mul_of_dvd_left hinv (intLabel a u - intLabel c v))
    have hid :
        (4 * b * e * (intLabel a u - intLabel c v)) * (36 * a * c * u * v) -
          ((4 * b * e) * (36 * a * c * u * v) - 1) *
            (intLabel a u - intLabel c v) =
        intLabel a u - intLabel c v := by ring
    rwa [hid] at h

/-- Two positive reduced ratios with the same cross product are the same ray. -/
theorem reduced_ray_unique (a b c e : ℕ)
    (ha : 0 < a) (hc : 0 < c)
    (hab : Nat.Coprime a b) (hce : Nat.Coprime c e)
    (h : a * e = c * b) : a = c ∧ b = e := by
  have hac : a ∣ c := hab.dvd_of_dvd_mul_right (by
    rw [← h]
    exact dvd_mul_right a e)
  have hca : c ∣ a := hce.dvd_of_dvd_mul_right (by
    rw [h]
    exact dvd_mul_right c b)
  have heq : a = c := Nat.dvd_antisymm hac hca
  subst c
  have hbe : b = e := (Nat.eq_of_mul_eq_mul_left ha h).symm
  exact ⟨rfl, hbe⟩

/-- Distinct positive primitive rays have a nonzero integer determinant. -/
theorem determinant_ne_zero (a b c e : ℕ)
    (ha : 0 < a) (hc : 0 < c)
    (hab : Nat.Coprime a b) (hce : Nat.Coprime c e)
    (hne : (a,b) ≠ (c,e)) :
    (a:ℤ)*(e:ℤ)-(c:ℤ)*(b:ℤ) ≠ 0 := by
  intro hzero
  have hcross : a*e = c*b := by
    exact_mod_cast (sub_eq_zero.mp hzero)
  obtain ⟨hac,hbe⟩ := reduced_ray_unique a b c e ha hc hab hce hcross
  exact hne (Prod.ext hac hbe)

theorem label_dvd_row_sq (a b u : ℕ) : label a u ∣ (row a b u) ^ 2 := by
  refine ⟨3 * b ^ 2 * u, ?_⟩
  dsimp [label, row]
  ring

theorem row_pos (a b u : ℕ) (ha : 0 < a) (hb : 0 < b) (hu : 0 < u) :
    0 < row a b u := by
  dsimp [row]
  positivity

theorem label_pos (a u : ℕ) (ha : 0 < a) (hu : 0 < u) : 0 < label a u := by
  dsimp [label]
  positivity

theorem label_lt_row (a b u : ℕ) (ha : 0 < a) (hu : 0 < u) (hab : a < b) :
    label a u < row a b u := by
  calc
    label a u = (3 * a * u) * a := by dsimp [label]; ring
    _ < (3 * a * u) * b := Nat.mul_lt_mul_of_pos_left hab (by positivity)
    _ = row a b u := by dsimp [row]; ring

theorem row_dvd_three (a b u : ℕ) : 3 ∣ row a b u := by
  refine ⟨a * b * u, ?_⟩
  dsimp [row]
  ring

theorem row_le_cutoff (B a b u : ℕ)
    (ha : a ≤ B) (hb : b ≤ B) (hu : u ≤ B ^ 6) :
    row a b u ≤ 3 * B ^ 8 := by
  calc
    row a b u ≤ 3 * B * B * B ^ 6 :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 3 ha) hb) hu
    _ = 3 * B ^ 8 := by ring

/-- No two distinct parameter triples with primitive rays encode the same packet. -/
theorem parameter_unique (a b c e u v : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hu : 0 < u)
    (hc : 0 < c) (he : 0 < e) (hv : 0 < v)
    (hab : Nat.Coprime a b) (hce : Nat.Coprime c e)
    (hM : row a b u = row c e v) (hs : label a u = label c v) :
    a = c ∧ b = e ∧ u = v := by
  have hcross : row a b u * (a * e) = row a b u * (c * b) := by
    calc
      row a b u * (a * e) = label a u * b * e := by dsimp [row, label]; ring
      _ = label c v * e * b := by rw [hs]; ring
      _ = row c e v * (c * b) := by dsimp [row, label]; ring
      _ = row a b u * (c * b) := by rw [hM]
  have hratio : a * e = c * b :=
    Nat.eq_of_mul_eq_mul_left (row_pos a b u ha hb hu) hcross
  obtain ⟨hac, hbe⟩ := reduced_ray_unique a b c e ha hc hab hce hratio
  subst c
  subst e
  have huv : u = v := Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 3 * a * b) hM
  exact ⟨rfl, rfl, huv⟩

/-- The upper bound on a nonzero determinant does not depend on the scale. -/
theorem determinant_abs_lt (B a b c e : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e)
    (haB : a ≤ B) (hbB : b ≤ B) (hcB : c ≤ B) (heB : e ≤ B) :
    |determinant a b c e| < B ^ 2 := by
  have hB : 0 ≤ B := le_trans (le_of_lt ha) haB
  have hae : a * e ≤ B ^ 2 := by
    simpa [pow_two] using mul_le_mul haB heB (le_of_lt he) hB
  have hcb : c * b ≤ B ^ 2 := by
    simpa [pow_two] using mul_le_mul hcB hbB (le_of_lt hb) hB
  have hpos₁ : 0 < a * e := mul_pos ha he
  have hpos₂ : 0 < c * b := mul_pos hc hb
  apply abs_lt.mpr
  dsimp [determinant]
  constructor <;> linarith

/-- A compatible divisor of a nonzero determinant is below the square cutoff. -/
theorem compatible_divisor_lt (B a b c e u v d : ℤ)
    (hdpos : 0 < d)
    (h₁ : d ∣ modulus a b u) (h₂ : d ∣ modulus c e v)
    (hcompat : d ∣ intLabel a u - intLabel c v)
    (hne : determinant a b c e ≠ 0)
    (hbound : |determinant a b c e| < B ^ 2) : d < B ^ 2 := by
  have hD := (full_modulus_compatibility a b c e u v d h₁ h₂).mp hcompat
  obtain ⟨k, hk⟩ := hD
  have hk0 : k ≠ 0 := by intro h; apply hne; simp [hk, h]
  have hkabs : (1 : ℤ) ≤ |k| := by
    have hpos : 0 < |k| := abs_pos.mpr hk0
    omega
  have hdle : d ≤ |determinant a b c e| := by
    rw [hk, abs_mul, abs_of_pos hdpos]
    nlinarith
  exact lt_of_le_of_lt hdle hbound

end Late
end PrimeAbundance
