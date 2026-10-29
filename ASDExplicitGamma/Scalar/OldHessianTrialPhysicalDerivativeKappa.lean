module

public import ASDExplicitGamma.Scalar.OldHessianTrialPhysicalScales
public import ASDExplicitGamma.Native.OldSignedDerivativeRowNumeric
public import ASDExplicitGamma.Numerics.Scalar.Lower

/-! The unchanged fine derivative row meets the frozen kappa certificate. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Algsuperdiff.Section3
open Numerics.Mirror Numerics.Scalar
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- The actual derivative row uses the original fine side 3^(-6)L,
regardless of the coarser source potential used in the admissible trial. -/
theorem old_hessian_physical_derivative_kappa (m : ℤ) (b : ℝ)
    (U : TriadicCube 2) (hU : U∈descendantsAtDepth (originCube 2 (m+129)) 134) :
    oldSignedDerivativeKappa (cubeScaleFactor U) b (q3ModelLength (m+1)).val≤
      evalReal scalarRealEnv lowerKappaExpr*|b| := by
  let L := q3ModelLength (m+1)
  rw [old_signed_derivative_kappa_shape (cubeScaleFactor U) b L.val L.property]
  have hh := mul_le_mul_of_nonneg_right
    (old_signed_derivative_shape_polynomial (div_nonneg (Triadic.cubeScaleFactor_pos' U).le L.property.le)) (abs_nonneg b)
  have hr : cubeScaleFactor U/L.val=1/(3:ℝ)^6 := by
    rw [cubeScaleFactor_descendant_eq_div_pow hU]
    exact old_hessian_physical_mesh_ratio m 5
  exact hh.trans_eq (by rw [hr]; norm_num [evalReal,lowerKappaExpr,sc])

end
end ASDExplicitGamma.Scalar
