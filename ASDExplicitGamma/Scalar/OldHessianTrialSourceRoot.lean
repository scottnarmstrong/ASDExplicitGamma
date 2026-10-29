module

public import ASDExplicitGamma.Scalar.OldHessianTrialCertifiedSource
public import ASDExplicitGamma.Native.OldSignedSqrtExpectation

/-! The full source root pays its single mixed d bill in the original law. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Cold Algsuperdiff.Section3
open Numerics.Mirror Numerics.Scalar
noncomputable section

/-- Nonnegativity of the literal convergent grouped weak proxy. -/
theorem old_hessian_grouped_old_theta_nonneg (M : ABKModel 2) (m : ℤ)
    (ω : Cutoff.CutoffSample 2) : 0≤oldHessianGroupedOldTheta M m ω := by
  rw [old_hessian_grouped_old_theta_series]
  exact tsum_nonneg (fun j => old_hessian_grouped_old_theta_term_nonneg M m j ω)

end
end ASDExplicitGamma.Scalar
