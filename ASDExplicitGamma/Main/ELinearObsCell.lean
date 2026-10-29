module

public import ASDExplicitGamma.Main.ELinearObsBridge
public import ASDExplicitGamma.Main.ELinearCorrector

/-! Cell-level history carriers and corrector payment for an arbitrary source
cell of scale `m-5`, from the cell's own frame field. -/

@[expose] public section

namespace ASDExplicitGamma.Main

attribute [local irreducible] Homogenization.descendantsAtDepth

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
  ASDExplicitGamma.Native ASDExplicitGamma.Response ASDExplicitGamma.Scalar
  ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open scoped ENNReal

noncomputable section

private theorem e_linear_openCube_translate
    (z : Fin 2 → ℤ) (Q : TriadicCube 2) :
    openCubeSet (translateCube z Q) =
      translateSet (nativeHeatCubeTranslationVector z Q) (openCubeSet Q) := by
  ext x
  rw [mem_translateSet_iff_sub_mem, mem_openCubeSet_translateCube_iff]
  rfl

private theorem e_linear_translateCube_origin (U : TriadicCube 2) :
    translateCube U.index (originCube 2 U.scale) = U := by
  cases U
  simp only [translateCube, originCube, Pi.zero_apply, zero_add]

private theorem e_linear_vec_eq_shift (U : TriadicCube 2) :
    nativeHeatCubeTranslationVector U.index (originCube 2 U.scale) =
      triadicCubeShift U := by
  ext i
  simp [nativeHeatCubeTranslationVector, triadicCubeShift, cubeScaleFactor,
    originCube]

theorem main_eosc_local_shifted_carrier_scale
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n ≤ m, nativeInductionState M h n)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (U : TriadicCube 2)
    (hscale : U.scale = m - 5) :
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


/-- The corrector history of a source cell, from the root frame field, is the
corrector history of the origin cell at the translated sample. -/
theorem main_e_linear_obs_corrector_translate
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : CutoffSample 2)
    (U : TriadicCube 2) :
    oldSignedCorrectorHistory U (responseFramePlanarCoefficientField M.nu
        (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t U ω)) =
      oldSignedCorrectorHistory (originCube 2 U.scale)
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
          (mainInsertionSkewCoefficient m t (originCube 2 U.scale)
            (Cutoff.translateCutoffSample (triadicCubeShift U) ω))) := by
  let Q : TriadicCube 2 := originCube 2 U.scale
  let z : Vec 2 := triadicCubeShift U
  let σ : ℝ := Annealed.sigmaBar M m
  let aU : CoeffField 2 := responseFramePlanarCoefficientField M.nu σ
    (mainInsertionSkewCoefficient m t U ω)
  let a0 : CoeffField 2 := responseFramePlanarCoefficientField M.nu σ
    (mainInsertionSkewCoefficient m t Q (Cutoff.translateCutoffSample z ω))
  let aBack : CoeffField 2 := translateCoeffField (-z) a0
  have hUcube : translateCube U.index Q = U := e_linear_translateCube_origin U
  have hvec : nativeHeatCubeTranslationVector U.index Q = z := e_linear_vec_eq_shift U
  have hcube : openCubeSet U = translateSet z (openCubeSet Q) := by
    rw [← hUcube, e_linear_openCube_translate, hvec]
  have hEllU := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet U) M.nu σ M.nu_pos
    (Annealed.sigmaBar_characterization M m).1
    (mainInsertionSkewCoefficient m t U ω)
  have hEll0 := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) M.nu σ M.nu_pos
    (Annealed.sigmaBar_characterization M m).1
    (mainInsertionSkewCoefficient m t Q (Cutoff.translateCutoffSample z ω))
  have hsetBack : translateSet (-z) (openCubeSet U) = openCubeSet Q := by
    ext x
    rw [mem_translateSet_iff_sub_mem, hcube, mem_translateSet_iff_sub_mem]
    simp [sub_eq_add_neg, add_assoc]
  have hEllBack : IsEllipticFieldOn _ _ (openCubeSet U) aBack :=
    fixedNu_field_translate (-z) (a := a0) (by
      rw [hsetBack]
      exact hEll0)
  have hcoef : aU =ᵐ[volumeMeasureOn (openCubeSet U)] aBack := by
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet U)] with x hx
    have hx0 : x - z ∈ openCubeSet Q := by
      rw [hcube, mem_translateSet_iff_sub_mem] at hx
      exact hx
    have hUval := main_eosc_response_frame_eq_scaled_partial M m t U ω x hx
    have h0val := main_eosc_response_frame_eq_scaled_partial
      M m t Q (Cutoff.translateCutoffSample z ω) (x - z) hx0
    have hpartial :
        (Model.partialInsertedCoefficient M m t
          (Cutoff.translateCutoffSample z ω)).toFun (x - z) =
        (Model.partialInsertedCoefficient M m t ω).toFun x := by
      rw [main_partialInsertedCoefficient_translate]
      simp [translateReg, sub_eq_add_neg, add_assoc]
    have hBackEval : aBack x =
        responseFramePlanarCoefficientField M.nu σ
          (mainInsertionSkewCoefficient m t Q
            (Cutoff.translateCutoffSample z ω)) (x - z) := by
      dsimp [aBack, a0]
      simp only [translateCoeffField]
      congr 1
    change responseFramePlanarCoefficientField M.nu σ
        (mainInsertionSkewCoefficient m t U ω) x = aBack x
    rw [hUval, hBackEval]
    have h0val' :
        responseFramePlanarCoefficientField M.nu σ
          (mainInsertionSkewCoefficient m t Q
            (Cutoff.translateCutoffSample z ω)) (x - z) =
        σ⁻¹ • (Model.partialInsertedCoefficient M m t
          (Cutoff.translateCutoffSample z ω)).toFun (x - z) := by
      simpa only [σ] using h0val
    rw [h0val', hpartial]
  have hcorr := (old_signed_histories_congr U aU aBack hEllU hEllBack hcoef).2.2
  have hback : aBack =
      translateCoeffField (-nativeHeatCubeTranslationVector U.index Q) a0 := by
    dsimp [aBack, z]
    rw [hvec]
  have hRoot : oldSignedCorrectorHistory U aBack = oldSignedCorrectorHistory Q a0 := by
    rw [← hUcube, hback]
    exact old_signed_correctorHistory_translateCube U.index Q a0
  exact hcorr.trans hRoot


/-- Actual-law payment of the corrector history of each depth-five cell by an
integrable majorant of mean at most `D m₀ H`. -/
theorem main_e_linear_obs_corrector_majorant
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n ≤ m, nativeInductionState M h n)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (U : TriadicCube 2) (hscale : U.scale = m - 5) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    ∃ C : CutoffSample 2 → ℝ, Integrable C μ ∧ 0 ≤ᵐ[μ] C ∧
      (∫ ω, C ω ∂μ) ≤ mainD * mainM0 (mainEnvelopeH (theta M) M.gamma t) *
        mainEnvelopeH (theta M) M.gamma t ∧
      ∀ᵐ ω ∂μ, oldSignedCorrectorHistory U (responseFramePlanarCoefficientField M.nu
        (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t U ω)) ≤ C ω := by
  intro μ
  let shift : CutoffSample 2 → CutoffSample 2 := fun ω =>
    Cutoff.translateCutoffSample (triadicCubeShift U) ω
  have hmp : MeasurePreserving shift μ μ :=
    ⟨Cutoff.measurable_translateCutoffSample (triadicCubeShift U),
      Cutoff.map_translateCutoffSample_cutoffSampleLaw M (triadicCubeShift U)⟩
  have hEnvelope := main_ordinary_trace_max_history_memLp_two_le_mainEnvelopeH
    M h hM hγ m hpast t ht.1 ht.2
  have hfinite : ∀ᵐ ω ∂μ, mainPartialInsertedTraceMaxHistory M m t ω < ⊤ := by
    simpa only [mainPartialInsertedTraceMaxHistory,
      mainOrdinaryTraceMaxHistory, mainOrdinaryTraceDepthMax,
      Scalar.inverseHistoryDiscount, mainAlpha] using hEnvelope.1
  have hmem : MemLp (fun ω => (mainPartialInsertedTraceMaxHistory M m t ω).toReal) 2 μ := by
    simpa only [mainPartialInsertedTraceMaxHistory,
      mainOrdinaryTraceMaxHistory, mainOrdinaryTraceDepthMax,
      Scalar.inverseHistoryDiscount, mainAlpha] using hEnvelope.2.1
  have hMultiplier := main_multiplier_moments_of_main_envelope_h
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


/-- Actual-law carriers of the inverse and response histories of a
depth-five cell: the translated inverse-bank maximum and multiplier history,
with their `L²` caps and joint first moment. -/
theorem main_e_linear_obs_history_carriers
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n ≤ m, nativeInductionState M h n)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (U : TriadicCube 2) (hscale : U.scale = m - 5) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    ∃ B Mu : CutoffSample 2 → ℝ,
      (∀ ω, 0 ≤ B ω) ∧ 0 ≤ᵐ[μ] Mu ∧
      MemLp B 2 μ ∧ lpNorm B 2 μ ≤ mainBeta ∧
      MemLp Mu 2 μ ∧ lpNorm Mu 2 μ ≤ mainM0 (mainEnvelopeH (theta M) M.gamma t) ∧
      (∫ ω, B ω * Mu ω ∂μ) ≤
        mainBeta * mainM0 (mainEnvelopeH (theta M) M.gamma t) ∧
      ∀ᵐ ω ∂μ,
        oldSignedInverseHistory U (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t U ω)) ≤ B ω ∧
        oldSignedResponseHistory U (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t U ω)) = Mu ω := by
  intro μ
  let shift : CutoffSample 2 → CutoffSample 2 := fun ω =>
    Cutoff.translateCutoffSample (triadicCubeShift U) ω
  have hmom := main_eosc_shifted_carrier_moments M h hM hγ m hpast t ht U
  have hprod := main_eosc_shifted_carrier_product_moment M h hM hγ m hpast t ht U
  have hloc := main_eosc_local_shifted_carrier_scale M h hM hγ m hpast t ht U hscale
  have hMultiplier := main_multiplier_moments_of_main_envelope_h
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
