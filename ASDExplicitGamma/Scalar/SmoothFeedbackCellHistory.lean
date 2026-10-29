/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Scalar.SmoothFeedbackAnnealed
public import ASDExplicitGamma.Main.MultiplierMoments
public import ASDExplicitGamma.Main.EOscillationCellHistoryTranslation
public import ASDExplicitGamma.Main.EOscillationResponseHistory

/-! The full-response history `M_U` of every side-`(m-5)` cell, with its
`L²` moments in the OLD law, transported from the origin cell by translation
invariance of the cutoff law. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization
open ASDExplicitGamma.Main ASDExplicitGamma.Native ASDExplicitGamma.Response
open ASDExplicitGamma.Triadic ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian
open Algsuperdiff.Section3
open scoped ENNReal

noncomputable section

/-- The `t = 0` insertion skew coefficient is the OLD skew coefficient. -/
theorem insertion_skew_zero (m : ℤ) (Q : TriadicCube 2) (ω : Cutoff.CutoffSample 2) :
    mainInsertionSkewCoefficient m 0 Q ω = oldCutoffSkewCoefficient m Q ω := by
  apply BoundedContinuousFunction.ext
  intro x
  simp [mainInsertionSkewCoefficient, oldCutoffSkewCoefficient]

/-- The actual response history of a cell in the OLD frame. -/
noncomputable def cellResponseHistory (M : ABKModel 2) (m : ℤ) (U : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  oldSignedResponseHistory U
    (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
      (oldCutoffSkewCoefficient m U ω))

theorem cell_history_eq_origin (M : ABKModel 2) (m : ℤ) (U : TriadicCube 2)
    (hU : U.scale = m - 5) (ω : Cutoff.CutoffSample 2) :
    cellResponseHistory M m U ω =
      mainPartialInsertedMultiplierHistory M m 0
        (Cutoff.translateCutoffSample (triadicCubeShift U) ω) := by
  have h1 := (main_eosc_local_histories_translate_origin M m 0 U ω).2
  have h2 := main_eosc_response_history_eq_multiplier_history M m 0
    (Cutoff.translateCutoffSample (triadicCubeShift U) ω)
  unfold cellResponseHistory
  rw [← insertion_skew_zero m U ω, h1]
  rw [hU] at h1 ⊢
  exact h2

/-- `L²` moment of the cell history. -/
theorem cell_history_L2 (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n ≤ m, nativeInductionState M h n) (U : TriadicCube 2)
    (hU : U.scale = m - 5) :
    eLpNorm (fun ω => cellResponseHistory M m U ω) 2
        (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (mainM0 (mainEnvelopeH (theta M) M.gamma 0)) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have hmom := main_multiplier_moments_of_main_envelope_h M h hM hγ m hpast 0
    le_rfl zero_le_one
  have hnorm := hmom.1.1.2
  have hmem := hmom.1.2
  have hmeas := main_partial_inserted_multiplier_history_aemeasurable M m 0
    ⟨le_rfl, zero_le_one⟩
  let z : Vec 2 := triadicCubeShift U
  have hfun : (fun ω => cellResponseHistory M m U ω) =
      (fun ω => mainPartialInsertedMultiplierHistory M m 0 ω) ∘
        (MeasurableEquiv.vadd z : Cutoff.CutoffSample 2 ≃ᵐ Cutoff.CutoffSample 2) := by
    funext ω
    exact cell_history_eq_origin M m U hU ω
  rw [hfun]
  have hmp : MeasurePreserving
      (MeasurableEquiv.vadd z : Cutoff.CutoffSample 2 ≃ᵐ Cutoff.CutoffSample 2) μ μ :=
    MeasureTheory.measurePreserving_vadd z μ
  rw [eLpNorm_comp_measurePreserving hmeas.aestronglyMeasurable hmp]
  have hle : (eLpNorm (fun ω => mainPartialInsertedMultiplierHistory M m 0 ω) 2 μ).toReal ≤
      mainM0 (mainEnvelopeH (theta M) M.gamma 0) := hnorm
  rw [← ENNReal.ofReal_toReal hmem.eLpNorm_ne_top]
  exact ENNReal.ofReal_le_ofReal hle

end

end ASDExplicitGamma.Scalar
