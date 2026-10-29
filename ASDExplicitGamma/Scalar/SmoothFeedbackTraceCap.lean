/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Scalar.SmoothFeedbackAnnealed
public import ASDExplicitGamma.Main.EnvelopeA

/-! The source hypothesis `sup_U E T_U <= a5` discharged on the side-`(m-5)`
cells from the accepted native source rows. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization
open Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Main
open ASDExplicitGamma.Native
attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

/-- On every cell of side `m-5`, the annealed trace excess is at most the exact
panel mean `a5 = mainSourceMeanPrefix` of the accepted source rows. -/
theorem smooth_feedback_cell_trace_mean_le_a5
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ k < N, nativeInductionState M h k)
    (m : ℤ) (hm : m < N) (U : TriadicCube 2) (hU : U.scale = m - 5) :
    (∫ ω, smoothFeedbackCellT M m U ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ mainSourceMeanPrefix := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have hid := Cold.coldNativeCellTrace_identDistrib M m U
  have hnn : ∀ ω, 0 ≤ cutoffTraceDefect M m U.scale ω := fun ω =>
    Cold.coldNativeCellTrace_nonneg M m (originCube 2 U.scale) ω
  have hmeas : AEStronglyMeasurable (cutoffTraceDefect M m U.scale) μ :=
    hid.aemeasurable_snd.aestronglyMeasurable
  have h1 : (∫ ω, smoothFeedbackCellT M m U ω ∂μ) =
      ∫ ω, cutoffTraceDefect M m U.scale ω ∂μ := hid.integral_eq
  have h2 : (∫ ω, cutoffTraceDefect M m U.scale ω ∂μ) =
      (∫⁻ ω, ENNReal.ofReal (cutoffTraceDefect M m U.scale ω) ∂μ).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnn) hmeas
  have hrows := ASDExplicitGamma.Native.native_source_rows M h hM hγ N hpast m hm
  have hcap := main_mean_actual_initial_cap M m hrows hγ
  rw [main_mean_actual_zero] at hcap
  rw [h1, h2, hU]
  have : m - 5 = m - ((5 : ℕ) : ℤ) := by norm_num
  rw [this]
  exact hcap

end

end ASDExplicitGamma.Scalar
