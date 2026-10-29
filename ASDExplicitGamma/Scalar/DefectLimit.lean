module

public import ASDExplicitGamma.Scalar.DefectShellCoupling
public import ASDExplicitGamma.Gaussian.GaussianFullConvergence
public import ASDExplicitGamma.Gaussian.H3SeriesCompletion
public import ASDExplicitGamma.Gaussian.Q3SeriesCovariance
public import ASDExplicitGamma.Gaussian.Q3H3Series

/-! Almost-sure convergence of the Wick partial sums of the shell field. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open MeasureTheory Filter ASDExplicitGamma.Gaussian Homogenization
open scoped Topology

noncomputable section

theorem ae_partial_tendsto (a b c d β : ℝ) (L : {l : ℝ // 0 < l}) :
    ∀ᵐ x ∂standardGaussianInfinitePi,
      Tendsto (fun n => ∑ i ∈ Finset.range n, x i •
        q3H3RangeValue a b c d β L (q3H3Directions a b c d β L whiteBasis i)) atTop
        (𝓝 ((q3C1Series a b c d β L whiteBasis x) 0)) := by
  filter_upwards [ae_tendsto_q3H3Series_full a b c d β L whiteBasis] with x hx
  have hT := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => _) 0).continuous.tendsto _).comp hx.2
  refine hT.congr' (Eventually.of_forall fun n => ?_)
  simp [q3H3RangeValue, gaussianPartialSum]

end

end ASDExplicitGamma.Scalar
