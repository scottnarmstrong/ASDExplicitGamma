module

public import ASDExplicitGamma.Gaussian.ObservedCovariance

/-! # Observation variances identify laws of Hilbert-series coefficient fields -/

@[expose] public section

open MeasureTheory Homogenization

namespace ASDExplicitGamma.Gaussian

/-- It is enough to compare all continuous linear observation variances. -/
theorem seriesLaw_eq_of_variance {V K : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    [TopologicalSpace K] [CompactSpace K] [SecondCountableTopology K] [LocallyCompactSpace K]
    (v w : ℕ → V) (hv : Summable (fun j => ‖v j‖ ^ 2)) (hw : Summable (fun j => ‖w j‖ ^ 2))
    (T : V →L[ℝ] C(K, ℝ))
    (hvar : ∀ A : C(K, ℝ) →L[ℝ] ℝ, (∑' j, (A (T (v j))) ^ 2) = ∑' j, (A (T (w j))) ^ 2) :
    standardGaussianInfinitePi.map (gaussianSeriesLimitE hv T) =
      standardGaussianInfinitePi.map (gaussianSeriesLimitE hw T) := by
  apply measure_eq_of_continuousMap_eval_linearCombination
  intro τ _ x t
  let A : C(K, ℝ) →L[ℝ] ℝ := ∑ i, t i • ContinuousMap.evalCLM ℝ (x i)
  have hA : continuousMapEvalLinearCombination τ x t = A := by
    funext f
    simp only [continuousMapEvalLinearCombination, A, sum_apply, smul_apply, smul_eq_mul,
      ContinuousMap.evalCLM_apply]
  rw [hA, Measure.map_map A.continuous.measurable
    (stronglyMeasurable_gaussianSeriesLimitE hv T).measurable,
    Measure.map_map A.continuous.measurable (stronglyMeasurable_gaussianSeriesLimitE hw T).measurable]
  change standardGaussianInfinitePi.map (fun ω => A (gaussianSeriesLimitE hv T ω)) =
    standardGaussianInfinitePi.map (fun ω => A (gaussianSeriesLimitE hw T ω))
  rw [map_gaussianSeriesLimitE_linear hv T A, map_gaussianSeriesLimitE_linear hw T A, hvar A]

end ASDExplicitGamma.Gaussian
