module

public import ASDExplicitGamma.Scalar.OldHessianTrialPrincipalCancellation

/-! Exact signed frozen covariance algebra. The covariance remainder is
retained, before any estimate or annealed directional contraction. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Response
noncomputable section

/-- The two quarter turns give a negative leading local affine pairing.
Both the scalar principal part and the deterministic covariance error are
kept with their exact coefficients and signs. -/
theorem old_hessian_frozen_affine_split (z : Fin 2 → Vec 2)
    (T E : Mat 2) (v lam : ℝ) :
    2*lam*(∑ i : Fin 2,vecDot (matVecMul responsePlanarJ (z i))
      (matVecMul T (matVecMul ((v/2) • responsePlanarJ+E) (basisVec i)))) =
      -lam*v*(∑ i : Fin 2,vecDot (z i)
        (matVecMul responsePlanarJ (matVecMul T (matVecMul responsePlanarJ (basisVec i)))))-
      2*lam*(∑ i : Fin 2,vecDot (z i)
        (matVecMul responsePlanarJ (matVecMul T (matVecMul E (basisVec i))))) := by
  simp only [Fin.sum_univ_two,vecDot,matVecMul,responsePlanarJ,Matrix.add_apply,
    Matrix.smul_apply,smul_eq_mul,basisVec,Pi.single_apply,Matrix.of_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  norm_num
  ring

end
end ASDExplicitGamma.Scalar
