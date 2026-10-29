module

public import ASDExplicitGamma.Native.GenericSourceBandInverseW
public import ASDExplicitGamma.Native.GenericSourceRefinedNorms
public import ASDExplicitGamma.Inverse.RawShellBandBankInputs

public import ASDExplicitGamma.Native.NativeBandWeight

/-! Actual probability-space norm factors on the simultaneous source band. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic
open scoped ENNReal
noncomputable section

variable {W : NativeAmp}

/-- The simultaneous source scalar is a measurable random continuous field. -/
theorem native_source_band_scalar_measurable_W (n : ℤ) (height : ℕ) (t : ℝ) :
    Measurable (nativeSourceBandScalar_W W n height t) := by
  let K := closure (cubeSet (originCube 2 n))
  obtain ⟨ell,hK⟩ := exists_originCube_containing_compact K
    (isBounded_cubeSet (originCube 2 n)).isCompact_closure
  have hs : Measurable (fun ω : Cutoff.CutoffSample 2 => Real.sqrt t •
      modelBandW K (nativeSourceBandIndex n height) (nativeSourceBandCoef_W W n height) ω) := by
    have he : ((fun _ : Cutoff.CutoffSample 2 => Real.sqrt t) •
        modelBandW K (nativeSourceBandIndex n height) (nativeSourceBandCoef_W W n height)) =
        (fun ω => Real.sqrt t • modelBandW K (nativeSourceBandIndex n height) (nativeSourceBandCoef_W W n height) ω) := by
      funext ω
      rfl
    rw [←he]
    exact
      (measurable_const : Measurable (fun _ : Cutoff.CutoffSample 2 => Real.sqrt t)).smul
        (measurable_modelBandW K (nativeSourceBandIndex n height) (nativeSourceBandCoef_W W n height))
  exact (measurable_olderField K ell n hK).add hs

/-- The real version of the complete band local history is measurable. -/
theorem native_source_band_history_toReal_measurable_W (M : ABKModel 2) (n : ℤ)
    (height : ℕ) (t : ℝ) : Measurable (fun ω => (nativeSourceBandHistory_W W M n height t ω).toReal) :=
  raw_shell_weighted_local_history_measurable M n (n+(height:ℤ)) (nativeAttW W t)

/-- Reuse the arbitrary-weight local bank for the real simultaneous majorant. -/
theorem native_source_band_history_toReal_L128_W
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (height : ℕ)
    (hpast : ∀ j < n, nativeInductionState M h j) (t : ℝ) (ht1 : t ≤ 1) :
    eLpNorm (fun ω => (nativeSourceBandHistory_W W M n height t ω).toReal) 128
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (3683/2500:ℝ) :=
  raw_shell_weighted_local_history_L128 M h hM hg n (n+(height:ℤ)) (by omega)
    (nativeAttW W t) (fun k _ => nativeAttW_mem W ht1 k) hpast

/-- All unrefined p20 factors on the actual simultaneous law are supplied
by the local/full banks; no actual-law norm premise remains. -/
theorem native_source_band_raw_factors_W
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (height : ℕ)
    (hpast : ∀ j < n, nativeInductionState M h j) (t : ℝ) (ht1 : t ≤ 1) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let σ : ℝ := Annealed.sigmaBar M n
    let X := nativeSourceBandScalar_W W n height t
    let T := fun ω => modelTraceObservable n M.nu σ (X ω)
    let F := fun ω => T ω+4
    let P := fun ω => (nativeSourceBandHistory_W W M n height t ω).toReal
    let D := fun ω => bankInverseTraceObservable n M.nu σ M.nu_pos
      (Annealed.sigmaBar_characterization M n).1 (X ω)
    MemLp T (ENNReal.ofReal 20) μ ∧ MemLp D (ENNReal.ofReal 20) μ ∧
    MemLp (fun ω => P ω*F ω) (ENNReal.ofReal 20) μ ∧
    MemLp (fun ω => (P ω)^2*F ω) (ENNReal.ofReal 20) μ ∧
    positiveLpNorm μ 20 T ≤ rawTraceFullResponseCap M.gamma height ∧
    positiveLpNorm μ 20 D ≤ 2*(3683/2500:ℝ) ∧
    positiveLpNorm μ 20 (fun ω => P ω*F ω) ≤ (3683/2500:ℝ)*rawTraceFullResponseCap M.gamma height ∧
    positiveLpNorm μ 20 (fun ω => (P ω)^2*F ω) ≤ (3683/2500:ℝ)^2*rawTraceFullResponseCap M.gamma height := by
  dsimp only
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let σ : ℝ := Annealed.sigmaBar M n
  let X := nativeSourceBandScalar_W W n height t
  let T := fun ω => modelTraceObservable n M.nu σ (X ω)
  let F := fun ω => T ω+4
  let P := fun ω => (nativeSourceBandHistory_W W M n height t ω).toReal
  let D := fun ω => bankInverseTraceObservable n M.nu σ M.nu_pos
    (Annealed.sigmaBar_characterization M n).1 (X ω)
  have hσ := (Annealed.sigmaBar_characterization M n).1
  have hX := native_source_band_scalar_measurable_W (W := W) n height t
  have hT : AEStronglyMeasurable T μ :=
    ((modelTraceObservable_hasPolynomiallyBoundedC2Derivatives n M.nu σ M.nu_pos hσ).1.continuous.measurable.comp hX).aestronglyMeasurable
  have hD : AEStronglyMeasurable D μ :=
    ((bank_inverse_trace_observable_C2 n M.nu σ M.nu_pos hσ).1.continuous.measurable.comp hX).aestronglyMeasurable
  have hF : AEStronglyMeasurable F μ := hT.add aestronglyMeasurable_const
  have hP : AEStronglyMeasurable P μ :=
    (native_source_band_history_toReal_measurable_W M n height t).aestronglyMeasurable
  have hP0 (ω) : 0 ≤ P ω := ENNReal.toReal_nonneg
  have hT0 (ω) : 0 ≤ T ω := modelTraceObservable_nonneg n M.nu σ M.nu_pos hσ _
  have hF0 (ω) : 0 ≤ F ω := add_nonneg (hT0 ω) (by norm_num)
  have hD0 (ω) : 0 ≤ D ω := native_source_model_inverse_trace_nonneg n M.nu σ M.nu_pos hσ _
  have hTF : ∀ᵐ ω ∂μ, T ω ≤ F ω := Filter.Eventually.of_forall fun ω => by dsimp [F]; linarith
  exact raw_trace_p20_bank_holder_caps μ P F T D M.gamma height M.shellPrefix.gamma_pos.le
    hP0 hF0 hT0 hD0 hTF (native_source_band_inverse_trace_ae_le_W M h hM hg n height hpast t ht1)
    hP hF hT hD (native_source_band_history_toReal_L128_W M h hM hg n height hpast t ht1)
    (native_source_band_full_response_L128_W M h hM hg n height hpast t ht1)

end
end ASDExplicitGamma.Native
