module

public import ASDExplicitGamma.Scalar.OldHessianTrialFrozenErrorFrobenius
public import ASDExplicitGamma.Native.OldSignedFlatOscillationCaps
public import ASDExplicitGamma.Scalar.OldHessianTrialPhysicalScales
public import ASDExplicitGamma.Native.OldSignedQ1FlatConstants

/-! The retained finite-parent covariance error with its exact mesh bill. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main
open Numerics.Mirror Numerics.Scalar
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- The sharp pi factor fits the source's .319 coefficient. -/
theorem old_hessian_inverse_pi_le_319 : 1/Real.pi≤(319/1000:ℝ) := by
  apply (div_le_iff₀ Real.pi_pos).2
  have hp : (157/50:ℝ)≤Real.pi := by linarith only [Real.pi_gt_d2]
  exact (by norm_num : (1:ℝ)≤(319/1000)*(157/50)).trans
    (mul_le_mul_of_nonneg_left hp (by norm_num))

end
end ASDExplicitGamma.Scalar
