module

public import ASDExplicitGamma.Scalar.Lambda8CovarianceAdapter
public import ASDExplicitGamma.Gaussian.SupMeanFirstMoments
public import ASDExplicitGamma.Scalar.Lambda8HessianPoincare
public import ASDExplicitGamma.Scalar.Lambda8ProjectionRegularity
public import ASDExplicitGamma.Response.FrameAlgebra
public import ASDExplicitGamma.Numerics.Scalar.Readable

/-! The actual q3 one-shell input bounds for Lambda8. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory ProbabilityTheory Homogenization
open ASDExplicitGamma.Triadic ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open ASDExplicitGamma.Response
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3

noncomputable section

/-- The six-level scale ratio used for the one-load oscillation input. -/
def lambda8Rho : ℝ := (3 : ℝ) ^ (-6 : ℤ)

/-- The outward rounded quarter-order coefficient in the one-load estimate. -/
def lambda8DeltaN : ℝ := (467 / 1000 : ℝ) * lambda8Rho * Real.sqrt (78 / 5 : ℝ)

theorem lambda8DeltaN_sq :
    lambda8DeltaN ^ 2 = (467 / 1000 : ℝ) ^ 2 * lambda8Rho ^ 2 * (78 / 5 : ℝ) := by
  rw [lambda8DeltaN]
  unfold lambda8Rho
  rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 78 / 5)]

end
end ASDExplicitGamma.Scalar
