module

public import ASDExplicitGamma.Main.ThetaGeneratorHotCovExpect
public import ASDExplicitGamma.Main.ThetaGeneratorHotCovXi
public import ASDExplicitGamma.Main.ThetaGeneratorHotCovNode
public import ASDExplicitGamma.Main.ThetaGeneratorHotCovExpectG
public import ASDExplicitGamma.Main.HotCovTrial
public import ASDExplicitGamma.Main.AffineFlatBoundary
public import ASDExplicitGamma.Main.ErrorCoefficients

/-! MA-E-COVARIANCE (hot-patched trial, observer root): the theorem, with the residual
factor `sqrt (v + B0/4)` that the actual flat means carry. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
  ASDExplicitGamma.Native ASDExplicitGamma.Response ASDExplicitGamma.Scalar
  ASDExplicitGamma.Triadic ASDExplicitGamma.Variational ASDExplicitGamma.Inverse
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff

noncomputable section

theorem hotCov_alg_ecov_Th (xi S R : ℝ) (hxi : 0 ≤ xi) (hS : 0 ≤ S) :
    2 * R * Real.sqrt (xi / 2 * S) = Real.sqrt 2 * Real.sqrt xi * R * Real.sqrt S := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rw [Real.sqrt_mul (by positivity), Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 2)]
  field_simp
  rw [h2]
  ring

end

end ASDExplicitGamma.Main
