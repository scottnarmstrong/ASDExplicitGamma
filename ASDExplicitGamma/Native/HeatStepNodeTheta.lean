module

public import ASDExplicitGamma.Native.HeatStepThetaPasses
public import ASDExplicitGamma.Native.HeatStepCapYTheta
public import ASDExplicitGamma.Native.HeatStepNode

/-! The theta-scaled NA-REFINED-HEAT conclusion for `ns` inserted shells, `9 ≤ ns ≤ 160`: the
physical parent trace in the frame `σ̄_{m+1}` is bounded in `L^20` by `θ · Y₄₈` and in mean by
`θ ·` the producer's mean return, given the theta-scaled start row. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Set Homogenization Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Numerics.Native
open scoped ENNReal

section ThetaNode

variable (ns : ℕ) [NeZero ns] (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ)

/-- A theta-scaled average-norm cap is a normalized uniform moment cap. -/
theorem nativeHeatStep_curveN_cap_of_avgNorm_theta (hns : ns ≤ 1331) (hg : M.gamma ≤ gammaZero)
    (hpast : ∀ l < m + 1, nativeInductionState M h l) (y : ℚ) (hy : 0 ≤ y)
    (hA : ∀ t ∈ Ioo (0 : ℝ) 1,
      (nativeHeatQ3RefinedCarrierSourceAverageNormGen ns) M h hM m
        (nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m ns)
        (nativeHeatTheta : ℝ) t ≤ theta M * (y : ℝ)) :
    HeatUniformMomentCap (nativeHeatStepCurveN ns M h hM m) y := by
  obtain ⟨hτ0, hτ1⟩ := theta_pos_le_one M hg
  refine ⟨hy, ?_⟩
  have hcont : ContinuousOn (nativeHeatStepCurveN ns M h hM m 20) (Icc (0 : ℝ) 1) :=
    nativeHeatStep_curveN_contOn ns M h hM m hg 20 le_rfl
  have hopen : ∀ t ∈ Ioo (0 : ℝ) 1,
      nativeHeatStepCurveN ns M h hM m 20 t ≤ (fun _ : ℝ => (y : ℝ) ^ 20) t := by
    intro t ht
    have hm := nativeHeatStep_moment_le_of_avgNorm_le ns M h hM m hns hg hpast t ht
      (theta M * (y : ℝ)) (hA t ht)
    unfold nativeHeatStepCurveN
    rw [nativeHeatStep_curve_eq_moment ns M h hM m 20 (by norm_num),
      div_le_iff₀ (pow_pos hτ0 20), mul_comm]
    simpa only [mul_pow] using hm
  exact nativeHeatStep_le_on_Icc_of_Ioo hcont continuousOn_const hopen

/-- The theta-scaled node, given the theta-scaled start row. -/
theorem nativeRefinedHeatStep_theta_of_start (hns9 : 9 ≤ ns) (hns160 : ns ≤ 160)
    (hg : M.gamma ≤ gammaZero)
    (hpast : ∀ j < m + 1, nativeInductionState M h j)
    (hstate : nativeInductionState M h (m + 1))
    (hstart : ∀ j ≤ 20, nativeHeatStepCurve ns M h hM m j 0 ≤
      theta M ^ j * ((nativeHeatInitGen ns).getD j 0 : ℚ)) :
    eLpNorm (nativeHeatStepParentTrace M m ns) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (theta M * (((nativeHeatY48Gen ns : ℚ)) : ℝ)) ∧
      ∫ ω, nativeHeatStepParentTrace M m ns ω ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
        theta M * (((nativeHeatMeanGen ns : ℚ)) : ℝ) := by
  obtain ⟨hτ0, hτ1⟩ := theta_pos_le_one M hg
  have hnum := nativeHeatStepPassNum_Gen ns hns9 hns160
  have hfr := nativeHeatStepFrameNum_Gen ns hns9 hns160
  have hind := nativeHeatStepIndivNum_Gen ns hns9 hns160
  have hgen := nativeHeatGenNum_of_range ns hns9 hns160
  have hchild := nativeHeatStep_childAllTime_theta ns hns9 hns160 M h hM hg m hpast
  have hX := nativeHeatStep_xCap_theta ns hnum hfr hgen M h hM hg m hpast hstate hchild
  have hF := nativeHeatStep_rawCap ns hns9 hns160 hnum hfr hind hgen M h hM hg m hstate
  have hYavg := nativeHeatStep_yCap_theta ns M h hM m hnum hfr hgen hg hpast hstate hchild
  have hY0 := nativeHeatStep_curveN_cap_of_avgNorm_theta ns M h hM m (by omega) hg hpast _
    hnum.y_nonneg hYavg
  have hY48 := nativeHeatStep_passesTheta_cap ns M h hM m hns9 hns160 hnum hgen hg hpast hstate
    hX hF hstart hY0
  have hmean := nativeHeatStep_meanTheta ns M h hM m hns9 hns160 hnum hgen hg hpast hstate
    hX hF hstart hY48
  refine ⟨?_, ?_⟩
  · have hm20 : nativeHeatStepMoment ns M h hM m 20 1 ≤
        (theta M * ((nativeHeatY48Gen ns : ℚ) : ℝ)) ^ 20 := by
      have h1 := hY48.2 1 ⟨zero_le_one, le_rfl⟩
      unfold nativeHeatStepCurveN at h1
      rw [nativeHeatStep_curve_eq_moment ns M h hM m 20 (by norm_num),
        div_le_iff₀ (pow_pos hτ0 20), mul_comm] at h1
      simpa only [mul_pow] using h1
    have := nativeHeatStep_parent_L20_le ns M h hM m hg hpast
      (theta M * ((nativeHeatY48Gen ns : ℚ) : ℝ))
      (mul_nonneg hτ0.le (by exact_mod_cast hY48.1)) hm20
    exact this
  · have h1 : nativeHeatStepMoment ns M h hM m 1 1 ≤ theta M * (nativeHeatMeanGen ns : ℝ) := by
      have e : nativeHeatStepCurveN ns M h hM m 1 1 =
          nativeHeatStepMoment ns M h hM m 1 1 / theta M := by
        unfold nativeHeatStepCurveN
        rw [nativeHeatStep_curve_eq_moment ns M h hM m 1 (by norm_num), pow_one]
      rw [e, div_le_iff₀ hτ0, mul_comm] at hmean
      exact hmean
    exact nativeHeatStep_parent_mean_le ns M h hM m hg hpast _ h1

end ThetaNode

end ASDExplicitGamma.Native
