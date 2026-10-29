module

public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # The actual plateau cutoff on the unit square -/

@[expose] public section

namespace ASDExplicitGamma.Cold

open MeasureTheory Set

/-- The closed unit square, of area one. -/
def plateauUnitSquare : Set (Fin 2 → ℝ) := Icc (fun _ => 0) (fun _ => 1)

/-- The depth coordinate in the source definition of the plateau cutoff. -/
noncomputable def plateauSquareDepth (x : Fin 2 → ℝ) : ℝ :=
  1 - 2 * max |x 0 - 1 / 2| |x 1 - 1 / 2|

/-- CO-PLATEAU-P1's cutoff, on its entire spatial carrier. -/
noncomputable def plateauCutoff (x : Fin 2 → ℝ) : ℝ :=
  (12 / 7 : ℝ) * min (2 * plateauSquareDepth x) 1

/-- Continuity of the piecewise affine cutoff. -/
theorem continuous_plateauCutoff : Continuous plateauCutoff := by
  unfold plateauCutoff plateauSquareDepth
  fun_prop

/-- Nonnegativity on the unit square. -/
theorem plateauCutoff_nonneg {x : Fin 2 → ℝ} (hx : x ∈ plateauUnitSquare) :
    0 ≤ plateauCutoff x := by
  have hx0 : |x 0 - 1 / 2| ≤ (1 / 2 : ℝ) := by
    rw [abs_le]
    constructor <;> linarith only [hx.1 0, hx.2 0]
  have hx1 : |x 1 - 1 / 2| ≤ (1 / 2 : ℝ) := by
    rw [abs_le]
    constructor <;> linarith only [hx.1 1, hx.2 1]
  have hdepth : 0 ≤ plateauSquareDepth x := by
    unfold plateauSquareDepth
    have hmax := max_le hx0 hx1
    linarith only [hmax]
  exact mul_nonneg (by norm_num) (le_min (mul_nonneg (by norm_num) hdepth) (by norm_num))

/-- The source sup bound holds on the whole spatial carrier. -/
theorem plateauCutoff_le (x : Fin 2 → ℝ) : plateauCutoff x ≤ 12 / 7 := by
  have h := mul_le_mul_of_nonneg_left (min_le_right (2 * plateauSquareDepth x) 1)
    (by norm_num : (0 : ℝ) ≤ 12 / 7)
  simpa only [plateauCutoff, mul_one] using h

/-- Each nonnegative superlevel set is an explicitly shrunken square. -/
theorem plateauCutoff_superlevel {s : ℝ} (_hs : 0 ≤ s) (hsmax : s ≤ 12 / 7) :
    {x : Fin 2 → ℝ | s ≤ plateauCutoff x} =
      Icc (fun _ => 7 * s / 48) (fun _ => 1 - 7 * s / 48) := by
  ext x
  have hc : (0 : ℝ) < 12 / 7 := by norm_num
  have hlevel : s ≤ plateauCutoff x ↔
      max |x 0 - 1 / 2| |x 1 - 1 / 2| ≤ 1 / 2 - 7 * s / 48 := by
    constructor
    · intro h
      have h' : s ≤ (12 / 7 : ℝ) * (2 * plateauSquareDepth x) :=
        h.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hc.le)
      unfold plateauSquareDepth at h'
      linarith only [h']
    · intro h
      have h' : s / (12 / 7 : ℝ) ≤ min (2 * plateauSquareDepth x) 1 := by
        apply le_min
        · unfold plateauSquareDepth
          linarith only [h]
        · linarith only [hsmax]
      have hh := (div_le_iff₀ hc).mp h'
      simpa only [plateauCutoff, mul_comm] using hh
  have hcoord (y : ℝ) : |y - 1 / 2| ≤ 1 / 2 - 7 * s / 48 ↔
      7 * s / 48 ≤ y ∧ y ≤ 1 - 7 * s / 48 := by
    rw [abs_le]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith only [h1, h2]
  simp only [mem_ofPred_eq, hlevel, max_le_iff, hcoord, mem_Icc, Pi.le_def]
  constructor
  · rintro ⟨h0, h1⟩
    constructor <;> intro i <;> fin_cases i
    · exact h0.1
    · exact h1.1
    · exact h0.2
    · exact h1.2
  · rintro ⟨hl, hu⟩
    exact ⟨⟨hl 0, hu 0⟩, ⟨hl 1, hu 1⟩⟩

/-- The superlevel square lies in the original unit square. -/
theorem plateauCutoff_superlevel_subset {s : ℝ} (hs : 0 ≤ s) (hsmax : s ≤ 12 / 7) :
    {x : Fin 2 → ℝ | s ≤ plateauCutoff x} ⊆ plateauUnitSquare := by
  rw [plateauCutoff_superlevel hs hsmax]
  intro x hx
  constructor <;> intro i
  · linarith only [hx.1 i, hs]
  · linarith only [hx.2 i, hs]

/-- The elementary square-root integral at the plateau endpoint. -/
theorem integral_sqrt_plateau_endpoint :
    ∫ s in (0 : ℝ)..((12 / 7 : ℝ) ^ 2), Real.sqrt s = 1152 / 343 := by
  simp_rw [Real.sqrt_eq_rpow]
  rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < 1 / 2))]
  have he : (1 / 2 : ℝ) + 1 = 3 / 2 := by norm_num
  rw [he, ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 12 / 7) 2]
  norm_num

end ASDExplicitGamma.Cold
