module

public import ASDExplicitGamma.Gaussian.CovarianceTrace

/-! # Law independence of the response covariance trace -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace ASDExplicitGamma.Gaussian

/-- Any two Hilbert series realizations of the same fresh law give the same response trace.
In particular, passing to a centered/restricted covariance factor does not make the trace depend
on a choice of Gaussian coordinates or a Cameron–Martin basis. -/
theorem modelCovarianceTrace_eq_of_law {V W E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    [SecondCountableTopology W] [MeasurableSpace W] [BorelSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E)
    {w : ℕ → W} (hB : Summable (fun j => ‖w j‖ ^ 2)) (S : W →L[ℝ] E)
    (hlaw : standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T) =
      standardGaussianInfinitePi.map (gaussianSeriesLimitE hB S))
    {Φ : E → ℝ} (hΦ : HasPolynomiallyBoundedC2Derivatives Φ) (x : E) :
    modelCovarianceTrace Φ (fun j => T (v j)) x =
      modelCovarianceTrace Φ (fun j => S (w j)) x := by
  have heq : gaussianSeriesHeatAverage hA T Φ x = gaussianSeriesHeatAverage hB S Φ x := by
    funext t
    have hf : Continuous (fun z : E => Φ (x + Real.sqrt t • z)) :=
      hΦ.1.continuous.comp (continuous_const.add (continuous_const.smul continuous_id))
    calc
      gaussianSeriesHeatAverage hA T Φ x t =
          ∫ z, Φ (x + Real.sqrt t • z) ∂standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T) :=
        (integral_map (stronglyMeasurable_gaussianSeriesLimitE hA T).measurable.aemeasurable hf.aestronglyMeasurable).symm
      _ = ∫ z, Φ (x + Real.sqrt t • z) ∂standardGaussianInfinitePi.map (gaussianSeriesLimitE hB S) := by rw [hlaw]
      _ = gaussianSeriesHeatAverage hB S Φ x t :=
        integral_map (stronglyMeasurable_gaussianSeriesLimitE hB S).measurable.aemeasurable hf.aestronglyMeasurable
  have hdA := hasDerivWithinAt_gaussianSeriesHeatAverage_zero hA T Φ hΦ x
  have hdB := hasDerivWithinAt_gaussianSeriesHeatAverage_zero hB S Φ hΦ x
  rw [heq] at hdA
  have hder := (hdA.derivWithin (uniqueDiffWithinAt_Ici (0 : ℝ))).symm.trans
    (hdB.derivWithin (uniqueDiffWithinAt_Ici (0 : ℝ)))
  have htraceA : gaussianSeriesHeatTraceAverage hA T Φ x 0 = modelCovarianceTrace Φ (fun j => T (v j)) x := by
    simp [gaussianSeriesHeatTraceAverage, gaussianSeriesHeatTrace, gaussianSeriesHeatArgument, modelCovarianceTrace]
  have htraceB : gaussianSeriesHeatTraceAverage hB S Φ x 0 = modelCovarianceTrace Φ (fun j => S (w j)) x := by
    simp [gaussianSeriesHeatTraceAverage, gaussianSeriesHeatTrace, gaussianSeriesHeatArgument, modelCovarianceTrace]
  rw [htraceA, htraceB] at hder
  linarith only [hder]

end ASDExplicitGamma.Gaussian
