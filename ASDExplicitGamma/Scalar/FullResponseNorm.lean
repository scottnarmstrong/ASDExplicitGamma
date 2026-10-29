module

public import ASDExplicitGamma.Scalar.CoefficientFlux

/-! The genuine four-dimensional Euclidean operator norm of the full source response. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Response MeasureTheory
open scoped RealInnerProductSpace

/-- The source full-response operator norm, on the actual Euclidean doubled carrier. -/
noncomputable def fullResponseOperatorNorm (Q : TriadicCube 2) (a : CoeffField 2) : ℝ :=
  ‖HilbertBlockVec.applyBlockMat (coarseBlockMatrix (cubeSet Q) a)‖

/-- The full response norm is nonnegative. -/
theorem full_response_operator_norm_nonneg (Q : TriadicCube 2) (a : CoeffField 2) :
    0 ≤ fullResponseOperatorNorm Q a := by
  unfold fullResponseOperatorNorm
  exact norm_nonneg _

/-- The full Euclidean operator norm bounds every literal doubled quadratic form. -/
theorem block_quadratic_le_operator_norm (A : BlockMat 2) (P : BlockVec 2) :
    blockVecDot P (blockMatVecMul A P) ≤ ‖HilbertBlockVec.applyBlockMat A‖*blockVecDot P P := by
  let x := HilbertBlockVec.ofBlockVec P
  let B := HilbertBlockVec.applyBlockMat A
  have h1 := real_inner_le_norm x (B x)
  have h2 := mul_le_mul_of_nonneg_left (B.le_opNorm x) (norm_nonneg x)
  have h3 : ‖x‖*‖B x‖ ≤ ‖B‖*‖x‖^2 := by nlinarith only [h2]
  have h := h1.trans h3
  simpa only [x,B,HilbertBlockVec.inner_ofBlockVec_applyBlockMat,HilbertBlockVec.norm_sq_ofBlockVec] using h

/-- The source top-load quadratic cost is bounded by the full four-dimensional norm. -/
theorem top_response_quadratic_le_full_norm (Q : TriadicCube 2) (a : CoeffField 2) (e : Vec 2) :
    blockVecDot (e,0) (blockMatVecMul (coarseBlockMatrix (cubeSet Q) a) (e,0)) ≤
      fullResponseOperatorNorm Q a*vecNormSq e := by
  simpa only [fullResponseOperatorNorm,blockVecDot,vecDot_zero_left,add_zero,vecNormSq] using
    block_quadratic_le_operator_norm (coarseBlockMatrix (cubeSet Q) a) (e,0)

end ASDExplicitGamma.Scalar
