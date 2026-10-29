module

public import ASDExplicitGamma.Main.FlatFieldCellGeometry
public import ASDExplicitGamma.Main.ErrorCoefficients

/-! Bundle of the q3 flat-field traces and constants. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Triadic
open ASDExplicitGamma.Gaussian
open scoped BigOperators

noncomputable section

/-- The plus boundary coefficient from the flat-field source row. -/
def mainFlatBoundaryEPlus (v B0 : ℝ) : ℝ :=
  Real.sqrt (v * B0 / 2) +
    (319 / 1000) * Real.sqrt ((156 / 5) * mainA2 v) * mainOp v

/-- The minus boundary coefficient from the flat-field source row. -/
def mainFlatBoundaryEMinus (v B0 : ℝ) : ℝ :=
  Real.sqrt (v * B0 / 2) +
    (319 / 1000) * Real.sqrt ((156 / 5) * mainA2 v) * mainOm v

/-- The source `e_cov` is the Euclidean combination of the two boundary
coefficients. -/
theorem mainEcov_eq_flat_boundary_errors (v q : ℝ) :
    mainEcov v q = Real.sqrt
      ((mainFlatBoundaryEPlus v (v * q)) ^ 2 +
        (mainFlatBoundaryEMinus v (v * q)) ^ 2) := by
  rfl

/-- All MA-FLAT-FIELD outputs for the actual q3 flat fields on a square.
The parameters `b` and `v=b²` distinguish shell amplitude from variance. -/
theorem main_flat_field_q3_source_caps (Q : TriadicCube 2) (b : ℝ)
    (hb : 0 < b) :
    (∑' n : Gaussian.whiteBasisIndex,
      hilbertGradientEnergy Q (mainFlatPlusH1 Q b (mainFlatQ3Length Q) n).grad) ≤
        (1 + Real.sqrt 2) ^ 2 * mainFlatSigmaSq b (mainFlatQ3Length Q) ∧
    (∑' n : Gaussian.whiteBasisIndex,
      hilbertGradientEnergy Q (mainFlatMinusH1 Q b (mainFlatQ3Length Q) n).grad) =
        mainFlatSigmaSq b (mainFlatQ3Length Q) ∧
    Real.sqrt (∑' n : Gaussian.whiteBasisIndex,
      (hilbertPositiveCircHaarNorm Q
        ((3 : ℝ) ^ (2 * (1 / 4 : ℝ)))
        (mainFlatPlusH1 Q b (mainFlatQ3Length Q) n).toFun) ^ 2) ≤ mainOp (b ^ 2) ∧
    Real.sqrt (∑' n : Gaussian.whiteBasisIndex,
      (hilbertPositiveCircHaarNorm Q
        ((3 : ℝ) ^ (2 * (1 / 4 : ℝ)))
        (mainFlatMinusH1 Q b (mainFlatQ3Length Q) n).toFun) ^ 2) ≤ mainOm (b ^ 2) ∧
    mainFlatPlusCellVariance Q 0 b + mainFlatMinusCellVariance Q 0 b ≤
      (4 + 2 * Real.sqrt 2) * (31.2 : ℝ) * mainA2 (b ^ 2) / 9 := by
  have hplusH1 := mainFlatPlusGradientEnergy_tsum Q b (mainFlatQ3Length Q)
  have hminusH1 := mainFlatMinusGradientEnergy_tsum Q b (mainFlatQ3Length Q)
  have hplusOsc := mainFlatPlusOscillation_q3_shell Q b
  have hminusOsc := mainFlatMinusOscillation_q3_shell Q b
  have hcell := mainFlatCellVariance_q3_shell_lt Q 0 b hb.ne'
  rw [show (31.2 : ℝ) = 156 / 5 by norm_num] at hplusOsc hminusOsc
  refine ⟨hplusH1.2, hminusH1.2, ?_, ?_, hcell.le⟩
  · calc
      _ ≤ (1 + Real.sqrt 2) *
          ((440 / 1000 : ℝ) * Real.sqrt ((156 / 5) * mainA2 (b ^ 2))) := hplusOsc
      _ = mainOp (b ^ 2) := by unfold mainOp; ring
  · calc
      _ ≤ (440 / 1000 : ℝ) * Real.sqrt ((156 / 5) * mainA2 (b ^ 2)) := hminusOsc
      _ = mainOm (b ^ 2) := by unfold mainOm; ring

end

end ASDExplicitGamma.Main
