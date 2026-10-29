module

public import ASDExplicitGamma.Main.ELinearObsCell
public import ASDExplicitGamma.Main.EOscillationCellHistoryTranslationOfHist
public import ASDExplicitGamma.Main.EOscillationDepthFiveProfileOfHist
public import ASDExplicitGamma.Main.MultiplierMomentsOfHist

/-! Successors of `ELinearObsCell` declarations with the history envelope as a parameter `Hfun`. -/



@[expose] public section

namespace ASDExplicitGamma.Main

attribute [local irreducible] Homogenization.descendantsAtDepth

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
  ASDExplicitGamma.Native ASDExplicitGamma.Response ASDExplicitGamma.Scalar
  ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open scoped ENNReal

noncomputable section

/-- Successor of `main_e_linear_obs_corrector_majorant` with the history envelope `Hfun`. -/
theorem main_e_linear_obs_corrector_majorant_ofHist
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n ≤ m, nativeInductionState M h n)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (U : TriadicCube 2) (hscale : U.scale = m - 5)
    (Hfun : ℝ → ℝ)
    (hHist : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
        mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω < ⊤) ∧
      MemLp (fun ω => (mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω).toReal) 2
        (Cutoff.cutoffSampleLaw M).toMeasure ∧
      lpNorm (fun ω => (mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω).toReal) 2
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ Hfun s)
    :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    ∃ C : CutoffSample 2 → ℝ, Integrable C μ ∧ 0 ≤ᵐ[μ] C ∧
      (∫ ω, C ω ∂μ) ≤ mainD * mainM0 (Hfun t) *
        Hfun t ∧
      ∀ᵐ ω ∂μ, oldSignedCorrectorHistory U (responseFramePlanarCoefficientField M.nu
        (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t U ω)) ≤ C ω := by
  intro μ
  let shift : CutoffSample 2 → CutoffSample 2 := fun ω =>
    Cutoff.translateCutoffSample (triadicCubeShift U) ω
  have hmp : MeasurePreserving shift μ μ :=
    ⟨Cutoff.measurable_translateCutoffSample (triadicCubeShift U),
      Cutoff.map_translateCutoffSample_cutoffSampleLaw M (triadicCubeShift U)⟩
  have hEnvelope := hHist t ⟨ht.1, ht.2⟩
  have hfinite : ∀ᵐ ω ∂μ, mainPartialInsertedTraceMaxHistory M m t ω < ⊤ := by
    simpa only [mainPartialInsertedTraceMaxHistory,
      mainOrdinaryTraceMaxHistory, mainOrdinaryTraceDepthMax,
      Scalar.inverseHistoryDiscount, mainAlpha] using hEnvelope.1
  have hmem : MemLp (fun ω => (mainPartialInsertedTraceMaxHistory M m t ω).toReal) 2 μ := by
    simpa only [mainPartialInsertedTraceMaxHistory,
      mainOrdinaryTraceMaxHistory, mainOrdinaryTraceDepthMax,
      Scalar.inverseHistoryDiscount, mainAlpha] using hEnvelope.2.1
  have hMultiplier := main_multiplier_moments_of_main_envelope_h_ofHist (Hfun := Hfun) (hHist := hHist)
    M h hM hγ m hpast t ht.1 ht.2
  have hMmem : MemLp (mainPartialInsertedMultiplierHistory M m t) 2 μ := hMultiplier.1.2
  let f : CutoffSample 2 → ℝ := fun ω => mainD * mainPartialInsertedMultiplierHistory M m t ω *
    (mainPartialInsertedTraceMaxHistory M m t ω).toReal
  have hfint : Integrable f μ := by
    have h1 : Integrable (fun ω => mainPartialInsertedMultiplierHistory M m t ω *
        (mainPartialInsertedTraceMaxHistory M m t ω).toReal) μ :=
      hMmem.integrable_mul hmem
    have := h1.const_mul mainD
    refine this.congr (Filter.Eventually.of_forall (fun ω => ?_))
    simp only [f]
    ring
  have hf0 : 0 ≤ᵐ[μ] f := by
    filter_upwards [hMultiplier.2] with ω hω
    exact mul_nonneg (mul_nonneg (by unfold mainD mainAlpha; positivity) hω)
      ENNReal.toReal_nonneg
  refine ⟨fun ω => f (shift ω), hmp.integrable_comp_of_integrable hfint,
    hmp.quasiMeasurePreserving.ae hf0, ?_, ?_⟩
  · have hi := integral_map (μ := μ) (φ := shift) hmp.measurable.aemeasurable
      (by rw [hmp.map_eq]; exact hfint.1)
    rw [hmp.map_eq] at hi
    change (∫ ω, f (shift ω) ∂μ) ≤ _
    rw [← hi]
    exact hMultiplier.1.1.1.2
  · have hfin' := hmp.quasiMeasurePreserving.ae hfinite
    filter_upwards [hfin'] with ω hω
    rw [main_e_linear_obs_corrector_translate M m t ω U, hscale]
    exact main_directional_corrector_history_le_multiplier_product M m t ht (shift ω) hω

/-- Successor of `main_e_linear_obs_history_carriers` with the history envelope `Hfun`. -/
theorem main_e_linear_obs_history_carriers_ofHist
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n ≤ m, nativeInductionState M h n)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (U : TriadicCube 2) (hscale : U.scale = m - 5)
    (Hfun : ℝ → ℝ)
    (hHist : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
        mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω < ⊤) ∧
      MemLp (fun ω => (mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω).toReal) 2
        (Cutoff.cutoffSampleLaw M).toMeasure ∧
      lpNorm (fun ω => (mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω).toReal) 2
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ Hfun s)
    :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    ∃ B Mu : CutoffSample 2 → ℝ,
      (∀ ω, 0 ≤ B ω) ∧ 0 ≤ᵐ[μ] Mu ∧
      MemLp B 2 μ ∧ lpNorm B 2 μ ≤ mainBeta ∧
      MemLp Mu 2 μ ∧ lpNorm Mu 2 μ ≤ mainM0 (Hfun t) ∧
      (∫ ω, B ω * Mu ω ∂μ) ≤
        mainBeta * mainM0 (Hfun t) ∧
      ∀ᵐ ω ∂μ,
        oldSignedInverseHistory U (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t U ω)) ≤ B ω ∧
        oldSignedResponseHistory U (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t U ω)) = Mu ω := by
  intro μ
  let shift : CutoffSample 2 → CutoffSample 2 := fun ω =>
    Cutoff.translateCutoffSample (triadicCubeShift U) ω
  have hmom := main_eosc_shifted_carrier_moments_ofHist (Hfun := Hfun) (hHist := hHist) M h hM hγ m hpast t ht U
  have hprod := main_eosc_shifted_carrier_product_moment_ofHist (Hfun := Hfun) (hHist := hHist) M h hM hγ m hpast t ht U
  have hloc := main_eosc_local_shifted_carrier_scale M h hM hγ m hpast t ht U hscale
  have hMultiplier := main_multiplier_moments_of_main_envelope_h_ofHist (Hfun := Hfun) (hHist := hHist)
    M h hM hγ m hpast t ht.1 ht.2
  have hmp : MeasurePreserving shift μ μ :=
    ⟨Cutoff.measurable_translateCutoffSample (triadicCubeShift U),
      Cutoff.map_translateCutoffSample_cutoffSampleLaw M (triadicCubeShift U)⟩
  refine ⟨fun ω => (mainCutoffQ3SourceInverseBankMax M m t (shift ω)).toReal,
    mainPartialInsertedMultiplierHistory M m t ∘ shift,
    fun ω => ENNReal.toReal_nonneg, ?_, hmom.1, hmom.2.1, hmom.2.2.1, hmom.2.2.2,
    hprod, ?_⟩
  · exact hmp.quasiMeasurePreserving.ae hMultiplier.2
  · filter_upwards [hloc] with ω hω
    exact hω

end
end ASDExplicitGamma.Main
end
