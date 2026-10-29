module

public import ASDExplicitGamma.Gaussian.CovarianceTrace
public import ASDExplicitGamma.Gaussian.RealizationSeries

/-! # Exact physical center covariance (8.18) -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace ASDExplicitGamma.Gaussian

section
variable {V E : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E)

/-- Every scalar observation has its exact second moment, without a nonsingularity assumption. -/
theorem integral_observation_sq (L : E →L[ℝ] ℝ) :
    ∫ ω, (L (gaussianSeriesLimitE hA T ω)) ^ 2 ∂standardGaussianInfinitePi =
      ∑' j, (L (T (v j))) ^ 2 := by
  let X := fun ω => L (gaussianSeriesLimitE hA T ω)
  have hX : Measurable X := L.continuous.measurable.comp
    (stronglyMeasurable_gaussianSeriesLimitE hA T).measurable
  have hlaw := map_gaussianSeriesLimitE_linear hA T L
  have hmean : ∫ ω, X ω ∂standardGaussianInfinitePi = 0 := by
    have hm := integral_map (μ := standardGaussianInfinitePi) hX.aemeasurable measurable_id.aestronglyMeasurable
    simp only [id_eq] at hm
    rw [← hm, hlaw]
    exact integral_id_gaussianReal
  have hv : variance X standardGaussianInfinitePi = ∑' j, (L (T (v j))) ^ 2 := by
    rw [← variance_id_map hX.aemeasurable, hlaw, variance_id_gaussianReal,
      Real.coe_toNNReal _ (tsum_nonneg fun j => sq_nonneg _)]
  rw [variance_eq_integral hX.aemeasurable, hmean] at hv
  simpa only [sub_zero] using hv

/-- Physical cross covariance equals the complete factor sum, with all off-diagonal entries. -/
theorem integral_observations_mul (L M : E →L[ℝ] ℝ) :
    ∫ ω, L (gaussianSeriesLimitE hA T ω) * M (gaussianSeriesLimitE hA T ω)
      ∂standardGaussianInfinitePi = ∑' j, L (T (v j)) * M (T (v j)) := by
  let X := fun ω => L (gaussianSeriesLimitE hA T ω)
  let Y := fun ω => M (gaussianSeriesLimitE hA T ω)
  have hz : MemLp (gaussianSeriesLimitE hA T) 2 standardGaussianInfinitePi := by
    simpa only [ENNReal.ofReal_ofNat] using memLp_gaussianSeriesLimitE hA T (p := 2) (le_refl 2)
  have hx := hz.continuousLinearMap_comp L
  have hy := hz.continuousLinearMap_comp M
  have hxy : Integrable (fun ω => X ω * Y ω) standardGaussianInfinitePi := hx.integrable_mul hy
  have hint : ∫ ω, (X ω + Y ω) ^ 2 ∂standardGaussianInfinitePi =
      (∫ ω, X ω ^ 2 ∂standardGaussianInfinitePi) +
      2 * (∫ ω, X ω * Y ω ∂standardGaussianInfinitePi) +
      (∫ ω, Y ω ^ 2 ∂standardGaussianInfinitePi) := by
    have hp : (fun ω => (X ω + Y ω) ^ 2) = fun ω => X ω ^ 2 + 2 * (X ω * Y ω) + Y ω ^ 2 := by
      funext ω
      ring
    have hiX : Integrable (fun ω => X ω ^ 2) standardGaussianInfinitePi := hx.integrable_sq
    have hiY : Integrable (fun ω => Y ω ^ 2) standardGaussianInfinitePi := hy.integrable_sq
    have hiXY : Integrable (fun ω => X ω ^ 2 + 2 * (X ω * Y ω)) standardGaussianInfinitePi := hiX.add (hxy.const_mul 2)
    rw [hp, integral_add hiXY hiY, integral_add hiX (hxy.const_mul 2), integral_const_mul]
  have hL := summable_sq_norm_gaussianDirections hA (L.comp T)
  have hM := summable_sq_norm_gaussianDirections hA (M.comp T)
  have hL' : Summable (fun j => (L (T (v j))) ^ 2) := by simpa only [ContinuousLinearMap.comp_apply, Real.norm_eq_abs, sq_abs] using hL
  have hM' : Summable (fun j => (M (T (v j))) ^ 2) := by simpa only [ContinuousLinearMap.comp_apply, Real.norm_eq_abs, sq_abs] using hM
  let B : E →L[ℝ] E →L[ℝ] ℝ := L.smulRight M
  have hcross : Summable (fun j => L (T (v j)) * M (T (v j))) :=
    summable_bilinear_images hA B T T
  have hsum : (∑' j, ((L + M) (T (v j))) ^ 2) =
      (∑' j, (L (T (v j))) ^ 2) + 2 * (∑' j, L (T (v j)) * M (T (v j))) +
      (∑' j, (M (T (v j))) ^ 2) := by
    have hp : (fun j => ((L + M) (T (v j))) ^ 2) =
        fun j => (L (T (v j))) ^ 2 + 2 * (L (T (v j)) * M (T (v j))) + (M (T (v j))) ^ 2 := by
      funext j
      rw [add_apply]
      ring
    rw [hp, (hL'.add (hcross.mul_left 2)).tsum_add hM', hL'.tsum_add (hcross.mul_left 2), tsum_mul_left]
  have hplus := integral_observation_sq hA T (L + M)
  have hx2 := integral_observation_sq hA T L
  have hy2 := integral_observation_sq hA T M
  simp only [add_apply] at hplus hsum
  change (∫ ω, (X ω + Y ω) ^ 2 ∂standardGaussianInfinitePi) = _ at hplus
  change (∫ ω, X ω ^ 2 ∂standardGaussianInfinitePi) = _ at hx2
  change (∫ ω, Y ω ^ 2 ∂standardGaussianInfinitePi) = _ at hy2
  change (∫ ω, X ω * Y ω ∂standardGaussianInfinitePi) = _
  linarith only [hint, hsum, hplus, hx2, hy2]

end
end ASDExplicitGamma.Gaussian
