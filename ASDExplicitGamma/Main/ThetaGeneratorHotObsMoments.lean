module

public import ASDExplicitGamma.Main.ThetaGeneratorHotTrialExpectationsSplit
public import ASDExplicitGamma.Main.ThetaGeneratorHotObsDrop

/-! Package D at the observer root, part two: means and `L²` size of the observer
energy drop. -/

@[expose] public section

namespace ASDExplicitGamma.Main

attribute [local irreducible] Homogenization.descendantsAtDepth

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Model
open ASDExplicitGamma.Native ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
open ASDExplicitGamma.Variational ASDExplicitGamma.Response
open scoped ENNReal

noncomputable section

/-- `L²` size of a cell trace for any cell of scale `m - 5`. -/
theorem main_hot_obs_cell_trace_l2_Th
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n ≤ m, nativeInductionState M h n)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (U : TriadicCube 2) (hscale : U.scale = m - 5) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    MemLp (rawCubeFourLoadTrace M m U t) 2 μ ∧
      lpNorm (rawCubeFourLoadTrace M m U t) 2 μ ≤
        mainEnvelopeH (theta M) M.gamma t / (1 - mainAlpha) := by
  intro μ
  obtain ⟨hmem, hnorm⟩ := main_hot_origin_trace_l2_Th M h hM hγ m hpast t ht
  have hOrigin : MemLp (rawDepthFourLoadTrace M m U.scale t) 2 μ := by
    rw [hscale]
    exact hmem
  refine ⟨main_rawCubeFourLoadTrace_memLp_of_origin M m U t 2 hOrigin, ?_⟩
  rw [main_rawCubeFourLoadTrace_lpNorm_eq_origin M m U t 2 hOrigin, hscale]
  exact hnorm

/-- Law invariance: every cell trace has the origin-cell mean. -/
theorem main_hot_cell_trace_integral_Th
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (U : TriadicCube 2)
    (hint : Integrable (rawDepthFourLoadTrace M m U.scale t)
      (Cutoff.cutoffSampleLaw M).toMeasure) :
    Integrable (rawCubeFourLoadTrace M m U t) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω, rawCubeFourLoadTrace M m U t ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      ∫ ω, rawDepthFourLoadTrace M m U.scale t ω ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  have hmp : MeasurePreserving
      (fun ω : Cutoff.CutoffSample 2 => Cutoff.translateCutoffSample (triadicCubeShift U) ω)
      (Cutoff.cutoffSampleLaw M).toMeasure (Cutoff.cutoffSampleLaw M).toMeasure :=
    ⟨Cutoff.measurable_translateCutoffSample (triadicCubeShift U),
      Cutoff.map_translateCutoffSample_cutoffSampleLaw M (triadicCubeShift U)⟩
  have heq : rawCubeFourLoadTrace M m U t =
      fun ω => rawDepthFourLoadTrace M m U.scale t
        (Cutoff.translateCutoffSample (triadicCubeShift U) ω) := by
    funext ω
    exact main_rawCubeFourLoadTrace_translate_to_origin M m U t ω
  rw [heq]
  refine ⟨hmp.integrable_comp_of_integrable hint, ?_⟩
  have h := integral_map (μ := (Cutoff.cutoffSampleLaw M).toMeasure)
    (φ := fun ω : Cutoff.CutoffSample 2 => Cutoff.translateCutoffSample (triadicCubeShift U) ω)
    (f := rawDepthFourLoadTrace M m U.scale t) hmp.measurable.aemeasurable
    (by rw [hmp.map_eq]; exact hint.aestronglyMeasurable)
  rw [hmp.map_eq] at h
  exact h.symm

/-- The origin-cube trace mean is the heat-average of the model at that scale. -/
theorem main_hot_origin_trace_mean_Th (M : ABKModel 2) (m s : ℤ) (t : ℝ) :
    (∫ ω, rawCubeFourLoadTrace M m (originCube 2 s) t ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) = modelTraceHeatAverage s M m t := by
  unfold modelTraceHeatAverage rawCubeFourLoadTrace
  rfl

end

end ASDExplicitGamma.Main
