module

public import ASDExplicitGamma.Gaussian.ConcentrationMaxima

/-! Exact finite linear laws for the product standard Gaussian. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

/-- A standard Gaussian linear form has the exact centered law, including a zero
coefficient vector. This supplies the finite-realization concentration bridge. -/
theorem supMean_standard_linear_law {n : ℕ} (a : Fin n → ℝ) :
    (standardGaussianPi n).map (gaussianFiniteLinearForm a) =
      gaussianReal 0 (Real.toNNReal (∑ i, a i ^ 2)) := by
  let E := EuclideanSpace ℝ (Fin n)
  let v : E := WithLp.toLp 2 a
  let L : StrongDual ℝ E := innerSL ℝ v
  have hmap : (standardGaussianPi n).map (WithLp.toLp 2) = stdGaussian E := by
    simpa only [standardGaussianPi, E] using
      (map_pi_eq_stdGaussian (ι := Fin n))
  have heq : gaussianFiniteLinearForm a = L ∘ WithLp.toLp 2 := by
    funext x
    change (∑ i, a i * x i) = ⟪v, WithLp.toLp 2 x⟫
    rw [EuclideanSpace.inner_toLp_toLp]
    simp only [dotProduct, star_trivial, mul_comm]
  rw [heq, ← Measure.map_map (by fun_prop) (by fun_prop), hmap,
    IsGaussian.map_eq_gaussianReal L, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian]
  congr 2
  simp only [L, innerSL_apply_norm, v]
  exact EuclideanSpace.real_norm_sq_eq _

end ASDExplicitGamma.Gaussian
