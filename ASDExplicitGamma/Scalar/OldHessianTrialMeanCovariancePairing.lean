module

public import ASDExplicitGamma.Scalar.OldHessianTrialMeanCovariance

/-! Complete signed contraction of the actual frozen mean covariance.
Every entry series converges before the physical two-load sum is rearranged. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- Matrix action on a basis vector is its actual column. -/
theorem old_hessian_matrix_basis_column (A : Mat 2) (i : Fin 2) :
    matVecMul A (basisVec i)=fun k => A k i := by
  classical
  funext k
  simp [matVecMul,basisVec,Pi.single_apply]

end
end ASDExplicitGamma.Scalar
