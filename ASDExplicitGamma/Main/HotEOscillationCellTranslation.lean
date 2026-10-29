module

public import ASDExplicitGamma.Main.EOscillationCellHistoryTranslation

/-! The translated local histories on a source cell of scale `m - 5`, with the cell given only
by its scale (so that it may lie in any observer root `originCube 2 (m + hobs)`). -/

@[expose] public section

namespace ASDExplicitGamma.Main

attribute [local irreducible] Homogenization.descendantsAtDepth

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
  ASDExplicitGamma.Native ASDExplicitGamma.Response ASDExplicitGamma.Scalar
  ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open scoped ENNReal

noncomputable section

theorem main_eosc_local_shifted_carrier_hot
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n ≤ m, nativeInductionState M h n)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (U : TriadicCube 2)
    (hU : U.scale = m - 5) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      oldSignedInverseHistory U
          (responseFramePlanarCoefficientField M.nu
            (Annealed.sigmaBar M m : ℝ)
            (mainInsertionSkewCoefficient m t U ω)) ≤
        (mainCutoffQ3SourceInverseBankMax M m t
          (Cutoff.translateCutoffSample (triadicCubeShift U) ω)).toReal ∧
      oldSignedResponseHistory U
          (responseFramePlanarCoefficientField M.nu
            (Annealed.sigmaBar M m : ℝ)
            (mainInsertionSkewCoefficient m t U ω)) =
        mainPartialInsertedMultiplierHistory M m t
          (Cutoff.translateCutoffSample (triadicCubeShift U) ω) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let Q : TriadicCube 2 := originCube 2 (m - 5)
  let shift : CutoffSample 2 → CutoffSample 2 :=
    fun ω => Cutoff.translateCutoffSample (triadicCubeShift U) ω
  have hscale : U.scale = m - 5 := hU
  have hcube : originCube 2 U.scale = Q := by
    dsimp [Q]
    rw [hscale]
  have hlocal := main_eosc_local_histories_translate_origin M m t U
  have hlocalInv (ω : CutoffSample 2) :
      oldSignedInverseHistory U
          (responseFramePlanarCoefficientField M.nu
            (Annealed.sigmaBar M m : ℝ)
            (mainInsertionSkewCoefficient m t U ω)) =
        oldSignedInverseHistory Q
          (responseFramePlanarCoefficientField M.nu
            (Annealed.sigmaBar M m : ℝ)
            (mainInsertionSkewCoefficient m t Q (shift ω))) := by
    have hh := (hlocal ω).1
    rw [hcube] at hh
    simpa only [shift] using hh
  have hlocalResp (ω : CutoffSample 2) :
      oldSignedResponseHistory U
          (responseFramePlanarCoefficientField M.nu
            (Annealed.sigmaBar M m : ℝ)
            (mainInsertionSkewCoefficient m t U ω)) =
        oldSignedResponseHistory Q
          (responseFramePlanarCoefficientField M.nu
            (Annealed.sigmaBar M m : ℝ)
            (mainInsertionSkewCoefficient m t Q (shift ω))) := by
    have hh := (hlocal ω).2
    rw [hcube] at hh
    simpa only [shift] using hh
  have hBank := main_q3_source_inverse_bank_and_history M h hM hγ m
    (fun n hn => hpast n hn.le) t ht
  have hRootBank : ∀ᵐ ω ∂μ,
      oldSignedInverseHistory Q
          (responseFramePlanarCoefficientField M.nu
            (Annealed.sigmaBar M m : ℝ)
            (mainInsertionSkewCoefficient m t Q ω)) ≤
        (mainCutoffQ3SourceInverseBankMax M m t ω).toReal := by
    simpa only [Q] using hBank.2.2.2
  have hmp : MeasurePreserving shift μ μ := by
    exact ⟨Cutoff.measurable_translateCutoffSample (triadicCubeShift U),
      Cutoff.map_translateCutoffSample_cutoffSampleLaw M (triadicCubeShift U)⟩
  have hRootBankShift : ∀ᵐ ω ∂μ,
      oldSignedInverseHistory Q
          (responseFramePlanarCoefficientField M.nu
            (Annealed.sigmaBar M m : ℝ)
            (mainInsertionSkewCoefficient m t Q (shift ω))) ≤
        (mainCutoffQ3SourceInverseBankMax M m t (shift ω)).toReal := by
    exact hmp.quasiMeasurePreserving.ae hRootBank
  filter_upwards [hRootBankShift] with ω hω
  constructor
  · rw [hlocalInv]
    exact hω
  · rw [hlocalResp]
    exact main_eosc_response_history_eq_multiplier_history M m t (shift ω)


end
end ASDExplicitGamma.Main
