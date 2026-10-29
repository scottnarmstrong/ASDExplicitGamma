module

public import ASDExplicitGamma.Scalar.RefBudget
public import ASDExplicitGamma.Scalar.RefMinkowski
public import ASDExplicitGamma.Scalar.RefSplit
public import ASDExplicitGamma.Scalar.SmoothFeedbackNode
public import ASDExplicitGamma.Scalar.NewResolventDefectFormula

/-! The hΛ1 budget of the corrected defect, with the forced-part identification as the named
hypothesis `T4InterfaceR`. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
  ASDExplicitGamma.Native
open Algsuperdiff.Section3
open scoped BigOperators ENNReal

attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

theorem amp_sq (M : ABKModel 2) (h : ℝ) (m : ℤ) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hQ : openCubeSet (originCube 2 (m + 129)) ⊆ openRectangle a b c d) (e : Vec 2) :
    (finalCfg M h m hab hcd hQ e).amp ^ 2 =
      (h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * ((m + 1 : ℤ) : ℝ))) *
        (((finalCfg M h m hab hcd hQ e).σ ^ 2)⁻¹) := by
  change (q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2 = _
  unfold q3ModelAmplitude
  have h3 : ((3 : ℝ) ^ (M.gamma * ((m + 1 : ℤ) : ℝ))) ^ 2 =
      (3 : ℝ) ^ (2 * M.gamma * ((m + 1 : ℤ) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
    ring_nf
  have e1 : Real.rpow 3 (M.gamma * ((m + 1 : ℤ) : ℝ)) = (3 : ℝ) ^ (M.gamma * ((m + 1 : ℤ) : ℝ)) := rfl
  rw [e1, div_pow, mul_pow, h3]
  rw [div_eq_mul_inv]
  rfl

end

end ASDExplicitGamma.Scalar
