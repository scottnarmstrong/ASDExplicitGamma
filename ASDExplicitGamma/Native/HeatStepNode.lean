module

public import ASDExplicitGamma.Native.HeatStepCapY
public import ASDExplicitGamma.Native.HeatStepEndpoint
public import ASDExplicitGamma.Native.HeatStepChildCap
public import ASDExplicitGamma.Native.HeatStepDataGenDispatch

/-! NA-REFINED-HEAT for `ns` inserted shells, `9 ≤ ns ≤ 160`: the physical parent trace at the
completed cutoff `m+1+ns` in the frame `σ̄_{m+1}` is bounded in `L^20` by `min(Y₄₈, y₀)` and in
mean by the producer's mean return `nativeHeatResultGen ns`.  The only analytic input not
proved here is the all-time actual child cap `NativeHeatStepChildAllTimeCap` at the level
`y₀` (the source's attenuation-vector transport of the individual cooperative system). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Set Homogenization Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Numerics.Native
open scoped ENNReal

theorem nativeRefinedHeatStep_Gen (ns : ℕ) [NeZero ns] (hns9 : 9 ≤ ns) (hns160 : ns ≤ 160)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ j < m + 1, nativeInductionState M h j)
    (hstate : nativeInductionState M h (m + 1))
    (hchild : NativeHeatStepChildAllTimeCap M m ns (nativeHeatY0Gen ns : ℝ)) :
    eLpNorm (nativeHeatStepParentTrace M m ns) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (((nativeHeatResultGen ns).1 : ℚ) : ℝ) ∧
      ∫ ω, nativeHeatStepParentTrace M m ns ω ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
        (((nativeHeatResultGen ns).2 : ℚ) : ℝ) := by
  have hnum := nativeHeatStepPassNum_Gen ns hns9 hns160
  have hfr := nativeHeatStepFrameNum_Gen ns hns9 hns160
  have hind := nativeHeatStepIndivNum_Gen ns hns9 hns160
  have hgen := nativeHeatGenNum_of_range ns hns9 hns160
  have hX := nativeHeatStep_xCap ns hnum hfr hgen M h hM hg m hpast hstate hchild
  have hF := nativeHeatStep_rawCap ns hns9 hns160 hnum hfr hind hgen M h hM hg m hstate
  have hYavg := nativeHeatStep_yCap ns M h hM m hnum hfr hgen hg hpast hstate hchild
  have hY0 := nativeHeatStep_cap_of_avgNorm ns M h hM m (by omega) hg hpast _ hnum.y_nonneg
    hYavg
  have hY48 := nativeHeatStep_passes_cap ns M h hM m hns9 hns160 hnum hgen hg hpast hstate
    hX hF hY0
  have hmean := nativeHeatStep_mean ns M h hM m hns9 hns160 hnum hgen hg hpast hstate hX hF hY48
  have hcur : nativeHeatStepCurve ns M h hM m 20 1 = nativeHeatStepMoment ns M h hM m 20 1 := by
    rw [nativeHeatStep_curve_eq_moment ns M h hM m 20 (by norm_num)]
  refine ⟨?_, ?_⟩
  · have hm20 : nativeHeatStepMoment ns M h hM m 20 1 ≤ ((nativeHeatY48Gen ns : ℚ) : ℝ) ^ 20 := by
      have := hY48.2 1 ⟨by norm_num, le_rfl⟩
      rwa [hcur] at this
    have hA := nativeHeatStep_parent_L20_le ns M h hM m hg hpast _ (by exact_mod_cast hY48.1) hm20
    have hB : eLpNorm (nativeHeatStepParentTrace M m ns) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal ((nativeHeatY0Gen ns : ℚ) : ℝ) := by
      have havg := nativeHeatStep_childAverage_L20_le_y0 ns hns9 hns160 hind hfr M h hM hg m
        (fun j hj => hpast j (by omega)) (hpast m (by omega))
      haveI : IsProbabilityMeasure (Cutoff.cutoffSampleLaw M).toMeasure :=
        (Cutoff.cutoffSampleLaw M).property
      refine le_trans ?_ havg
      have hpm : AEStronglyMeasurable (nativeHeatStepParentTrace M m ns)
          (Cutoff.cutoffSampleLaw M).toMeasure :=
        (nativeHeatStep_trace_aemeasurable M (m + 1 + (ns : ℤ)) (originCube 2 (m + 10))
          (Annealed.sigmaBar M (m + 1) : ℝ)).aestronglyMeasurable
      refine eLpNorm_mono_ae_real hpm (f := nativeHeatStepParentTrace M m ns)
        (g := fun ω => ((9 ^ 10 : ℝ)⁻¹) * Finset.univ.sum (fun i => nativeHeatStepChildTraceCC M m ns i ω)) ?_
      filter_upwards with ω
      have h1 := nativeHeatStep_parent_le_average M m ns ω
      rw [Real.norm_of_nonneg h1.1]
      exact h1.2
    show _ ≤ ENNReal.ofReal ((min (nativeHeatY48Gen ns) (nativeHeatY0Gen ns) : ℚ) : ℝ)
    rcases le_total (nativeHeatY48Gen ns) (nativeHeatY0Gen ns) with hle | hle
    · rw [min_eq_left hle]; exact hA
    · rw [min_eq_right hle]; exact hB
  · exact nativeHeatStep_parent_mean_le ns M h hM m hg hpast _ hmean

end ASDExplicitGamma.Native

end
