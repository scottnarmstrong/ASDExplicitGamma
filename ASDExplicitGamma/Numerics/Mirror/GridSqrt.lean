module

public import ASDExplicitGamma.Numerics.Mirror.GridInterval
public import ASDExplicitGamma.Numerics.ExpSqrt
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Linarith

/-!
# Computed grid enclosures for square roots

The integer square-root algorithm supplies the grid endpoints. No endpoint witness is part of
the input or certificate.
-/

@[expose] public section

namespace ASDExplicitGamma.Numerics.Mirror

open ASDExplicitGamma.Numerics

/-- Integer below the scaled rational endpoint, for the lower square-root bracket. -/
def sqrtFloorUnits (G : ℕ) (q : ℚ) : ℕ :=
  Int.toNat ⌊q * (gridScale G) ^ 2⌋

/-- Integer above the scaled rational endpoint before taking its square root. -/
def sqrtCeilInputUnits (G : ℕ) (q : ℚ) : ℕ :=
  Int.toNat ⌈q * (gridScale G) ^ 2⌉

/-- The exact ceiling of the square root of the scaled upper endpoint. -/
def sqrtCeilUnits (G : ℕ) (q : ℚ) : ℕ :=
  let m := sqrtCeilInputUnits G q
  let k := Nat.sqrt m
  if k ^ 2 = m then k else k + 1

/-- Computed lower grid endpoint for `√q`. -/
def sqrtLower (G : ℕ) (q : ℚ) : ℚ :=
  (Nat.sqrt (sqrtFloorUnits G q) : ℚ) / gridScale G

/-- Computed upper grid endpoint for `√q`. -/
def sqrtUpper (G : ℕ) (q : ℚ) : ℚ :=
  (sqrtCeilUnits G q : ℚ) / gridScale G

theorem sqrtPoint_bounds (G : ℕ) {q : ℚ} (hq : 0 ≤ q) :
    (sqrtLower G q : ℝ) ≤ Real.sqrt q ∧ Real.sqrt q ≤ sqrtUpper G q := by
  let scale := gridScale G
  let loUnits := sqrtFloorUnits G q
  let hiInput := sqrtCeilInputUnits G q
  let hiUnits := sqrtCeilUnits G q
  have hscale : 0 < scale := gridScale_pos G
  have hsquare : 0 < scale ^ 2 := sq_pos_of_pos hscale
  have hscaledNonneg : 0 ≤ q * scale ^ 2 := mul_nonneg hq (sq_nonneg _)
  have hloInt : 0 ≤ ⌊q * scale ^ 2⌋ := Int.floor_nonneg.mpr hscaledNonneg
  have hhiInt : 0 ≤ ⌈q * scale ^ 2⌉ := Int.ceil_nonneg hscaledNonneg
  have hloUnits : (loUnits : ℚ) = (⌊q * scale ^ 2⌋ : ℤ) := by
    dsimp [loUnits, sqrtFloorUnits]
    exact_mod_cast Int.toNat_of_nonneg hloInt
  have hhiInput : (hiInput : ℚ) = (⌈q * scale ^ 2⌉ : ℤ) := by
    dsimp [hiInput, sqrtCeilInputUnits]
    exact_mod_cast Int.toNat_of_nonneg hhiInt
  have hhiRoot : (hiInput : ℚ) ≤ (hiUnits : ℚ) ^ 2 := by
    dsimp [hiUnits, sqrtCeilUnits]
    split_ifs with h
    · exact_mod_cast le_of_eq h.symm
    · exact_mod_cast Nat.le_of_lt (Nat.lt_succ_sqrt' (sqrtCeilInputUnits G q))
  have hloScaled : (Nat.sqrt loUnits : ℚ) ^ 2 ≤ q * scale ^ 2 := by
    calc
      (Nat.sqrt loUnits : ℚ) ^ 2 ≤ loUnits := by exact_mod_cast Nat.sqrt_le' loUnits
      _ = (⌊q * scale ^ 2⌋ : ℤ) := hloUnits
      _ ≤ q * scale ^ 2 := Int.floor_le _
  have hhiScaled : q * scale ^ 2 ≤ (hiUnits : ℚ) ^ 2 := by
    calc
      q * scale ^ 2 ≤ (⌈q * scale ^ 2⌉ : ℤ) := Int.le_ceil _
      _ = hiInput := hhiInput.symm
      _ ≤ (hiUnits : ℚ) ^ 2 := hhiRoot
  have hloSq : ((Nat.sqrt loUnits : ℚ) / scale) ^ 2 ≤ q := by
    rw [div_pow]
    exact (div_le_iff₀ hsquare).2 hloScaled
  have hhiSq : q ≤ ((hiUnits : ℚ) / scale) ^ 2 := by
    rw [div_pow]
    exact (le_div_iff₀ hsquare).2 hhiScaled
  have hlo0 : 0 ≤ (Nat.sqrt loUnits : ℚ) / scale := div_nonneg (Nat.cast_nonneg _) hscale.le
  have hhi0 : 0 ≤ (hiUnits : ℚ) / scale :=
    div_nonneg (Nat.cast_nonneg _) hscale.le
  have hbounds :
      ((Nat.sqrt loUnits : ℚ) / scale : ℝ) ≤ Real.sqrt q ∧
      Real.sqrt q ≤ ((hiUnits : ℚ) / scale : ℝ) :=
    by
      simpa only [Rat.cast_div] using sqrt_enclosure_rat hlo0 hhi0 hloSq hhiSq
  simpa [sqrtLower, sqrtUpper, loUnits, hiUnits, scale] using hbounds

/-- Computed grid enclosure for the square root of a nonnegative rational interval. -/
def sqrt (G : ℕ) (a : QInterval) (ha : 0 ≤ a.lo) : QInterval :=
  ⟨sqrtLower G a.lo, sqrtUpper G a.hi,
    by
      have hmono : Real.sqrt (a.lo : ℝ) ≤ Real.sqrt a.hi := by
        exact Real.sqrt_le_sqrt (by exact_mod_cast a.valid)
      have hreal : (sqrtLower G a.lo : ℝ) ≤ sqrtUpper G a.hi :=
        (sqrtPoint_bounds G ha).1.trans (hmono.trans (sqrtPoint_bounds G (ha.trans a.valid)).2)
      exact_mod_cast hreal⟩

theorem sqrt_sound (G : ℕ) {a : QInterval} {x : ℝ} (ha : 0 ≤ a.lo)
    (hx : QInterval.Contains a x) : QInterval.Contains (sqrt G a ha) (Real.sqrt x) := by
  change (a.lo : ℝ) ≤ x ∧ x ≤ a.hi at hx
  have hlo := (sqrtPoint_bounds G ha).1
  have hhi := (sqrtPoint_bounds G (ha.trans a.valid)).2
  have hlo' : (sqrtLower G a.lo : ℝ) ≤ Real.sqrt x :=
    hlo.trans (Real.sqrt_le_sqrt hx.1)
  have hhi' : Real.sqrt x ≤ sqrtUpper G a.hi :=
    (Real.sqrt_le_sqrt hx.2).trans hhi
  exact ⟨hlo', hhi'⟩

end ASDExplicitGamma.Numerics.Mirror
