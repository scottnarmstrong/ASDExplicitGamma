module

public import ASDExplicitGamma.Scalar.GaussianMoments
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-! The exact fourth moment of a centered real Gaussian, without independence. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Every centered Gaussian law is a scalar image of the standard Gaussian. -/
theorem gaussian_real_sqrt_scale (v : ℝ≥0) :
    (gaussianReal 0 1).map (fun x : ℝ => Real.sqrt (v:ℝ)*x) = gaussianReal 0 v := by
  rw [gaussianReal_map_const_mul]
  congr 1
  · exact mul_zero _
  · ext
    simp only [NNReal.coe_mk,mul_one,Real.sq_sqrt v.coe_nonneg]

/-- Transfer any natural moment through the actual scalar Gaussian law. -/
theorem gaussian_real_moment_scale (v : ℝ≥0) (n : ℕ) :
    (∫ x : ℝ, x^n ∂gaussianReal 0 v) = (Real.sqrt (v:ℝ))^n*standardGaussianMoment n := by
  rw [← gaussian_real_sqrt_scale v,integral_map (by fun_prop) (by fun_prop)]
  simp only [mul_pow,integral_const_mul,standardGaussianMoment]

/-- The centered Gaussian fourth moment is exactly three times the squared second moment. -/
theorem centered_gaussian_fourth_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (hX : HasGaussianLaw X μ) (hm : ∫ ω, X ω ∂μ = 0) :
    (∫ ω, (X ω)^4 ∂μ) = 3*(∫ ω, (X ω)^2 ∂μ)^2 := by
  have hn (n : ℕ) : (∫ ω, (X ω)^n ∂μ) =
      (Real.sqrt (Var[X;μ].toNNReal:ℝ))^n*standardGaussianMoment n := by
    have hlaw := hX.map_eq_gaussianReal
    rw [hm] at hlaw
    rw [← gaussian_real_moment_scale _ n,← hlaw,integral_map hX.aemeasurable (by fun_prop)]
  rw [hn 4,hn 2,standard_gaussian_even_moments.2.2.1,standard_gaussian_even_moments.2.1]
  ring

end ASDExplicitGamma.Scalar
