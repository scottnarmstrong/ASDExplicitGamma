module

public import ASDExplicitGamma.Scalar.CellResponseTest
public import ASDExplicitGamma.Scalar.CoefficientFlux
public import ASDExplicitGamma.Scalar.SmoothFeedbackCellRotation
public import ASDExplicitGamma.Scalar.SpatialQuarterTurnHaar
public import ASDExplicitGamma.Triadic.VectorHaarSymmetry

/-! Deterministic covariance of the actual affine directional Gram under a
centered planar quarter-turn. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory Variational ASDExplicitGamma.Triadic

/-- The vector action on an affine load induced by the cell quarter-turn. -/
noncomputable def quarterTurnVector (e : Vec 2) : Vec 2 :=
  matVecMul (Matrix.swap ℝ 0 1) (matVecMul (signFlipMatrix 0) e)

@[simp] theorem quarterTurnVector_zero (e : Vec 2) :
    quarterTurnVector e 0 = e 1 := by
  simp [quarterTurnVector, matVecMul_swap_eq_comp,
    matVecMul_signFlipMatrix_apply]

@[simp] theorem quarterTurnVector_one (e : Vec 2) :
    quarterTurnVector e 1 = -e 0 := by
  simp [quarterTurnVector, matVecMul_swap_eq_comp,
    matVecMul_signFlipMatrix_apply]

@[simp] theorem quarterTurnLoad_affine (e : Vec 2) :
    quarterTurnLoad (e, 0) = (quarterTurnVector e, 0) := by
  apply Prod.ext
  · rfl
  · change matVecMul (Matrix.swap ℝ 0 1)
      (matVecMul (signFlipMatrix 0) (0 : Vec 2)) = 0
    rw [matVecMul_zero, matVecMul_zero]

end ASDExplicitGamma.Scalar

end
