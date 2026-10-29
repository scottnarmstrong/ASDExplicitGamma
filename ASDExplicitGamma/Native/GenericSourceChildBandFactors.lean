module

public import ASDExplicitGamma.Native.GenericSourceChildBandResponse
public import ASDExplicitGamma.Native.GenericSourceRefinedNorms
public import ASDExplicitGamma.Inverse.RawShellBandBankInputs

/-! Actual probability-space norm factors on the simultaneous source band. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic
open scoped ENNReal
noncomputable section

/-- The simultaneous source scalar is a measurable random continuous field. -/
theorem native_source_child_band_scalar_measurable (n : ℤ) (height : ℕ) (t : ℝ) :
    Measurable (nativeSourceChildBandScalar n height t) := by
  let K := closure (cubeSet (originCube 2 (n-1)))
  obtain ⟨ell,hK⟩ := exists_originCube_containing_compact K
    (isBounded_cubeSet (originCube 2 (n-1))).isCompact_closure
  have hs : Measurable (fun ω : Cutoff.CutoffSample 2 => Real.sqrt t •
      modelBand K (nativeSourceBandIndex n height) ω) := by
    have he : ((fun _ : Cutoff.CutoffSample 2 => Real.sqrt t) •
        modelBand K (nativeSourceBandIndex n height)) =
        (fun ω => Real.sqrt t • modelBand K (nativeSourceBandIndex n height) ω) := by
      funext ω
      rfl
    rw [←he]
    exact
      (measurable_const : Measurable (fun _ : Cutoff.CutoffSample 2 => Real.sqrt t)).smul
        (measurable_modelBand K (nativeSourceBandIndex n height))
  exact (measurable_olderField K ell n hK).add hs

/-- The real version of the complete band local history is measurable. -/
theorem native_source_child_band_history_toReal_measurable (M : ABKModel 2) (n : ℤ)
    (height : ℕ) (t : ℝ) : Measurable (fun ω => (nativeSourceChildBandHistory M n height t ω).toReal) :=
  ENNReal.measurable_toReal.comp (history_finite_max_measurable _ _
    (fun Q => bank_root_inverse_history_measurable Q.1 M n (n+(height:ℤ)) (fun _ => Real.sqrt t)))

/-- Reuse the arbitrary-weight local bank for the real simultaneous majorant. -/
theorem native_source_child_band_history_toReal_L128
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (height : ℕ)
    (hpast : ∀ j < n, nativeInductionState M h j) (t : ℝ) (ht1 : t ≤ 1) :
    eLpNorm (fun ω => (nativeSourceChildBandHistory M n height t ω).toReal) 128
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (3683/2500:ℝ) := by
  have hb := native_source_child_band_local_bank M h hM hg n height hpast t ht1
  have he := eLpNorm_congr_ae (p := 128) (ofReal_toReal_ae_eq hb.history_finite)
  have he' : eLpNorm (fun ω => (nativeSourceChildBandHistory M n height t ω).toReal) 128
      (Cutoff.cutoffSampleLaw M).toMeasure =
      eLpNorm (nativeSourceChildBandHistory M n height t) 128 (Cutoff.cutoffSampleLaw M).toMeasure := by
    calc
      _ = eLpNorm (fun ω => ENNReal.ofReal (nativeSourceChildBandHistory M n height t ω).toReal) 128
          (Cutoff.cutoffSampleLaw M).toMeasure :=
        (eLpNorm_ofReal _ (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)).symm
      _ = _ := he
  rw [he']
  change eLpNorm (bankFiniteRootHistoryMax (bankLocalRoots (originCube 2 (n-1)) 4)
    M n (n+(height:ℤ)) (fun _ => Real.sqrt t)) 128 _ ≤ _
  simpa only [inverseBankCap,Rat.cast_div,Rat.cast_ofNat] using hb.total_L128

/-- All unrefined p20 factors on the actual simultaneous law are supplied
by the local/full banks; no actual-law norm premise remains. -/
theorem native_source_child_band_raw_factors
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (height : ℕ)
    (hpast : ∀ j < n, nativeInductionState M h j) (t : ℝ) (ht1 : t ≤ 1) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let σ : ℝ := Annealed.sigmaBar M n
    let X := nativeSourceChildBandScalar n height t
    let T := fun ω => modelTraceObservable (n-1) M.nu σ (X ω)
    let F := fun ω => T ω+4
    let P := fun ω => (nativeSourceChildBandHistory M n height t ω).toReal
    let D := fun ω => bankInverseTraceObservable (n-1) M.nu σ M.nu_pos
      (Annealed.sigmaBar_characterization M n).1 (X ω)
    MemLp T (ENNReal.ofReal 20) μ ∧ MemLp D (ENNReal.ofReal 20) μ ∧
    MemLp (fun ω => P ω*F ω) (ENNReal.ofReal 20) μ ∧
    MemLp (fun ω => (P ω)^2*F ω) (ENNReal.ofReal 20) μ ∧
    positiveLpNorm μ 20 T ≤ nativeSourceChildFullResponseCap M.gamma height ∧
    positiveLpNorm μ 20 D ≤ 2*(3683/2500:ℝ) ∧
    positiveLpNorm μ 20 (fun ω => P ω*F ω) ≤ (3683/2500:ℝ)*nativeSourceChildFullResponseCap M.gamma height ∧
    positiveLpNorm μ 20 (fun ω => (P ω)^2*F ω) ≤ (3683/2500:ℝ)^2*nativeSourceChildFullResponseCap M.gamma height := by
  dsimp only
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let σ : ℝ := Annealed.sigmaBar M n
  let X := nativeSourceChildBandScalar n height t
  let T := fun ω => modelTraceObservable (n-1) M.nu σ (X ω)
  let F := fun ω => T ω+4
  let P := fun ω => (nativeSourceChildBandHistory M n height t ω).toReal
  let D := fun ω => bankInverseTraceObservable (n-1) M.nu σ M.nu_pos
    (Annealed.sigmaBar_characterization M n).1 (X ω)
  have hσ := (Annealed.sigmaBar_characterization M n).1
  have hX := native_source_child_band_scalar_measurable n height t
  have hT : AEStronglyMeasurable T μ :=
    ((modelTraceObservable_hasPolynomiallyBoundedC2Derivatives (n-1) M.nu σ M.nu_pos hσ).1.continuous.measurable.comp hX).aestronglyMeasurable
  have hD : AEStronglyMeasurable D μ :=
    ((bank_inverse_trace_observable_C2 (n-1) M.nu σ M.nu_pos hσ).1.continuous.measurable.comp hX).aestronglyMeasurable
  have hF : AEStronglyMeasurable F μ := hT.add aestronglyMeasurable_const
  have hP : AEStronglyMeasurable P μ :=
    (native_source_child_band_history_toReal_measurable M n height t).aestronglyMeasurable
  have hP0 (ω) : 0 ≤ P ω := ENNReal.toReal_nonneg
  have hT0 (ω) : 0 ≤ T ω := modelTraceObservable_nonneg (n-1) M.nu σ M.nu_pos hσ _
  have hF0 (ω) : 0 ≤ F ω := add_nonneg (hT0 ω) (by norm_num)
  have hD0 (ω) : 0 ≤ D ω := native_source_model_inverse_trace_nonneg (n-1) M.nu σ M.nu_pos hσ _
  have hTF : ∀ᵐ ω ∂μ, T ω ≤ F ω := Filter.Eventually.of_forall fun ω => by dsimp [F]; linarith
  have hf : 0 ≤ nativeSourceChildFullResponseCap M.gamma height := by
    have hg0 := M.shellPrefix.gamma_pos.le
    dsimp [nativeSourceChildFullResponseCap]
    positivity
  exact raw_trace_p20_bank_holder_caps_of_cap μ P F T D (nativeSourceChildFullResponseCap M.gamma height) hf
    hP0 hF0 hT0 hD0 hTF (native_source_child_band_inverse_trace_ae_le M h hM hg n height hpast t ht1)
    hP hF hT hD (native_source_child_band_history_toReal_L128 M h hM hg n height hpast t ht1)
    (native_source_child_band_full_response_L128 M h hM hg n height hpast t ht1)

end
end ASDExplicitGamma.Native
