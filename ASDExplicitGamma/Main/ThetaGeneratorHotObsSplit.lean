module

public import ASDExplicitGamma.Main.ThetaGeneratorEnvelopeASlope
public import ASDExplicitGamma.Main.ThetaGeneratorHotTrialExpectationsDrop
public import ASDExplicitGamma.Main.ThetaGeneratorHotTrialExpectationsSplit
public import ASDExplicitGamma.Main.ThetaGeneratorHotObsDrop
public import ASDExplicitGamma.Main.ThetaGeneratorHotObsMoments
public import ASDExplicitGamma.Main.HotPositiveSplitGeneric

/-! Package D at the observer root, part three: `L²` size, mean, and the positive
splits of the observer energy drop. -/

@[expose] public section

namespace ASDExplicitGamma.Main

attribute [local irreducible] Homogenization.descendantsAtDepth

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Model
open ASDExplicitGamma.Native ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
open ASDExplicitGamma.Variational ASDExplicitGamma.Response
open scoped ENNReal

noncomputable section

/-- Cell traces on scale `m-5` cells: integrable with mean `a`. -/
theorem main_hot_obs_cell_trace_mean_Th
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n ≤ m, nativeInductionState M h n)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (U : TriadicCube 2) (hscale : U.scale = m - 5) :
    Integrable (rawCubeFourLoadTrace M m U t) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω, rawCubeFourLoadTrace M m U t ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      inSourceMeanActual M m 5 t := by
  have hl2 := (main_hot_obs_cell_trace_l2_Th M h hM hγ m hpast t ht U hscale).1
  obtain ⟨hmem0, -⟩ := main_hot_origin_trace_l2_Th M h hM hγ m hpast t ht
  have hint : Integrable (rawDepthFourLoadTrace M m U.scale t)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
    have : MemLp (rawDepthFourLoadTrace M m U.scale t) 2
        (Cutoff.cutoffSampleLaw M).toMeasure := by
      rw [hscale]
      exact hmem0
    exact this.integrable (by norm_num)
  obtain ⟨h1, h2⟩ := main_hot_cell_trace_integral_Th M m t U hint
  refine ⟨h1, ?_⟩
  rw [h2]
  have h3 := main_hot_origin_trace_mean_Th M m U.scale t
  change (∫ ω, rawCubeFourLoadTrace M m (originCube 2 U.scale) t ω
    ∂(Cutoff.cutoffSampleLaw M).toMeasure) = _
  rw [h3, hscale]
  unfold inSourceMeanActual
  norm_num

/-- Observer energy-drop mean: `E Δ = a − f_obs` with `f_obs` the observer-root mean, and
`E Δ ≤ mainEnvelopeA − f_obs`. -/
theorem main_hot_obs_energy_drop_identity_Th
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (hobs : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    Integrable (mainHotDropObs_Th M m hobs t) μ ∧
    (∫ ω, mainHotDropObs_Th M m hobs t ω ∂μ) =
      inSourceMeanActual M m 5 t - modelTraceHeatAverage (m + hobs) M m t ∧
    0 ≤ modelTraceHeatAverage (m + hobs) M m t ∧
    (∫ ω, mainHotDropObs_Th M m hobs t ω ∂μ) ≤
      mainEnvelopeA
        ((q3ModelAmplitude M h (m + 1)) ^ 2 /
          (Annealed.sigmaBar M m : ℝ) ^ 2)
        M.gamma (theta M * mainSourceMeanPrefix) t -
      modelTraceHeatAverage (m + hobs) M m t := by
  classical
  intro μ
  let Q := originCube 2 (m + hobs)
  let D := hobs + 5
  let T : TriadicCube 2 → Cutoff.CutoffSample 2 → ℝ :=
    fun U ω => rawCubeFourLoadTrace M m U t ω
  let a := inSourceMeanActual M m 5 t
  have hpastM : ∀ n ≤ m, nativeInductionState M h n :=
    fun n hn => hpast n (lt_of_le_of_lt hn hm)
  have hcell (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q D) :
      Integrable (T U) μ ∧ (∫ ω, T U ω ∂μ) = a :=
    main_hot_obs_cell_trace_mean_Th M h hM hγ m hpastM t ht U
      (hot_cell_scale_hot m hobs U hU)
  have hcard : ((descendantsAtDepth Q D).card : ℝ) ≠ 0 := by
    have hne : (descendantsAtDepth Q D).Nonempty :=
      ⟨_, originCube_mem_descendantsAtDepth' 2 (m + hobs) D⟩
    exact_mod_cast hne.card_pos.ne'
  have havgFun : (fun ω => descendantsAverage Q D (fun U => T U ω)) =
      fun ω => ((descendantsAtDepth Q D).card : ℝ)⁻¹ *
        ∑ U ∈ descendantsAtDepth Q D, T U ω := rfl
  have havgInt : Integrable (fun ω => descendantsAverage Q D (fun U => T U ω)) μ := by
    rw [havgFun]
    exact (integrable_finsetSum _ fun U hU => (hcell U hU).1).const_mul _
  have havgInteg : (∫ ω, descendantsAverage Q D (fun U => T U ω) ∂μ) = a := by
    rw [havgFun, integral_const_mul,
      integral_finsetSum _ fun U hU => (hcell U hU).1,
      Finset.sum_congr rfl fun U hU => (hcell U hU).2]
    simp only [Finset.sum_const, nsmul_eq_mul]
    field_simp
  have hΔnonneg (ω : Cutoff.CutoffSample 2) : 0 ≤ mainHotDropObs_Th M m hobs t ω :=
    (main_hot_drop_obs_pathwise_Th M m hobs t ω).2
  have hrootNonneg (ω : Cutoff.CutoffSample 2) : 0 ≤ T Q ω :=
    raw_cube_four_load_trace_nonneg M m Q t ⟨ht.1, ht.2⟩ ω
  have hrootLe (ω : Cutoff.CutoffSample 2) :
      T Q ω ≤ descendantsAverage Q D (fun U => T U ω) := by
    have := hΔnonneg ω
    unfold mainHotDropObs_Th at this
    exact sub_nonneg.mp this
  have hrootInt : Integrable (T Q) μ := by
    refine havgInt.mono' (main_hot_raw_cube_measurable_Th M m Q t).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_of_nonneg (hrootNonneg ω)]
    exact hrootLe ω
  have hfEq : (∫ ω, T Q ω ∂μ) = modelTraceHeatAverage (m + hobs) M m t :=
    main_hot_origin_trace_mean_Th M m (m + hobs) t
  have hΔint : Integrable (mainHotDropObs_Th M m hobs t) μ := havgInt.sub hrootInt
  have hΔeq : (∫ ω, mainHotDropObs_Th M m hobs t ω ∂μ) =
      a - modelTraceHeatAverage (m + hobs) M m t := by
    unfold mainHotDropObs_Th
    rw [integral_sub havgInt hrootInt, havgInteg, hfEq]
  have hf0 : 0 ≤ modelTraceHeatAverage (m + hobs) M m t := by
    rw [← hfEq]
    exact integral_nonneg hrootNonneg
  have hA := main_envelope_a_actual_law_Th M h hM hγ N hpast m hm ht
  refine ⟨hΔint, hΔeq, hf0, ?_⟩
  rw [hΔeq]
  have : a ≤ mainEnvelopeA
        ((q3ModelAmplitude M h (m + 1)) ^ 2 /
          (Annealed.sigmaBar M m : ℝ) ^ 2)
        M.gamma (theta M * mainSourceMeanPrefix) t := hA
  linarith

end

end ASDExplicitGamma.Main
