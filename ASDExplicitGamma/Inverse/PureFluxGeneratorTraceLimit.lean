module

public import ASDExplicitGamma.Gaussian.CovarianceTrace

/-! Passing uniform finite-direction signed generator estimates to covariance traces. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open ASDExplicitGamma.Gaussian
open scoped BigOperators
noncomputable section

theorem pureFlux_secondDirectionalDerivative_summable {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (hf : ContDiff ℝ 2 f) (H : ℕ → E)
    (hH : Summable (fun j => ‖H j‖^2)) (x : E) :
    Summable (fun j => secondDirectionalDerivative f x (H j)) := by
  have hs := summable_bilinear_images hH (fderiv ℝ (fderiv ℝ f) x)
    (ContinuousLinearMap.id ℝ E) (ContinuousLinearMap.id ℝ E)
  have heq (j : ℕ) : secondDirectionalDerivative f x (H j) =
      fderiv ℝ (fderiv ℝ f) x (H j) (H j) := second_fderiv_eq hf x (H j) (H j)
  simpa only [heq, ContinuousLinearMap.id_apply] using hs

/-- A signed summable family inherits a common bound on all finite sums. -/
theorem pureFlux_tsum_half_le_of_finite_bounds {ι : Type*} (g : ι → ℝ)
    (hg : Summable g) (C : ℝ)
    (hb : ∀ s : Finset ι, (1/2:ℝ)*(∑ j ∈ s, g j) ≤ C) :
    (1/2:ℝ)*(∑' j, g j) ≤ C := by
  have hs := hg.mul_left (1/2:ℝ)
  have hfinite (s : Finset ι) : ∑ j ∈ s, (1/2:ℝ)*g j ≤ C := by
    rw [← Finset.mul_sum]
    exact hb s
  simpa only [tsum_mul_left] using hs.tsum_le_of_sum_le hfinite

end
end ASDExplicitGamma.Inverse
