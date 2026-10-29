module

public import ASDExplicitGamma.Scalar.AmplitudeResponse
public import Algsuperdiff.Section3.Provider.ErrorComparison.ToLambdas
public import Algsuperdiff.Section3.Observable.CutoffCoarseBlockRepresentative

/-! The literal scalar-normalized doubled response depends only on the framed coarse matrix. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Variational Book.Ch04
open Algsuperdiff.Section3

/-- The scalar frame is exactly the inverse square-root load congruence. -/
theorem frameMatrix_eq_inverse_sqrt_congruence (A : BlockMat 2) (σ : ℝ) (hσ : 0 < σ) :
    frameMatrix σ A=coarseMatrixRescale (Real.sqrt σ)⁻¹ A := by
  have hs := Real.sq_sqrt hσ.le
  have hn := (Real.sqrt_pos.mpr hσ).ne'
  cases A with
  | mk ul ur ll lr =>
    simp only [frameMatrix,coarseMatrixRescale,BlockMat.mk.injEq]
    refine ⟨?_,trivial,trivial,?_⟩ <;> ext i j <;>
      simp only [Matrix.smul_apply,smul_eq_mul,zpow_neg,zpow_ofNat,inv_pow,inv_inv,hs]

/-- The actual Chapter 2 square-root normalizers produce the true framed quadratic response. -/
theorem normalized_block_quadratic_eq_frame (A : BlockMat 2) (σ : ℝ) (hσ : 0 < σ)
    (e : FullBlockVec 2) :
    blockJQuadraticFullBlockMat (toFullBlockMat A)
      (ofFullBlockVec (Matrix.mulVec (Book.Ch02.constantFullBlockMatrixInvSqrt (scalarMatrix σ)) e))
      (ofFullBlockVec (Matrix.mulVec (Book.Ch02.constantFullBlockMatrixSqrt (scalarMatrix σ)) e))=
    blockJQuadraticFullBlockMat (toFullBlockMat (frameMatrix σ A)) (ofFullBlockVec e) (ofFullBlockVec e) := by
  rw [Provider.ErrorComparison.ofFullBlockVec_constantFullBlockMatrixInvSqrt_scalarMatrix hσ,
    Provider.ErrorComparison.ofFullBlockVec_constantFullBlockMatrixSqrt_scalarMatrix hσ,
    frameMatrix_eq_inverse_sqrt_congruence A σ hσ]
  have h := blockJQuadratic_amplitude A (ofFullBlockVec e) (ofFullBlockVec e)
    (Real.sqrt σ)⁻¹ (inv_ne_zero (Real.sqrt_pos.mpr hσ).ne')
  simpa only [loadRescale,inv_inv,ofFullBlockVec] using h

end ASDExplicitGamma.Scalar
