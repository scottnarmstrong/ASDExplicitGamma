-- Ported from GMCExplicitDelta Proofs/ProjPoincare/Scalar.lean (Apache-2.0).
module

public import ASDExplicitGamma.Triadic.Support.Contract.DerivedGeometry
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Function.L2Space

/-! Duality on thirds: the one-dimensional projected Poincaré estimate. -/
@[expose] public section

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

namespace ASDExplicitGamma.Triadic.Support.ProjectedPoincare

/-- The real L² Cauchy--Schwarz inequality in an integral-only form. -/
theorem integral_mul_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * ∫ x, g x ^ 2 ∂μ := by
  have he {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
      inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
    rw [hx, hy]
    simp only [RCLike.inner_apply', starRingEnd_apply, star_trivial]
  have h := real_inner_mul_inner_self_le (hf.toLp f) (hg.toLp g)
  rw [he hf hg, he hf hf, he hg hg] at h
  simpa only [pow_two] using h

end ASDExplicitGamma.Triadic.Support.ProjectedPoincare
