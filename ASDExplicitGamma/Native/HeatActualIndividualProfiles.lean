module

public import ASDExplicitGamma.Native.HeatActualOldProfile
public import ASDExplicitGamma.Native.HeatCooperativeSourcePower

/-! Actual trace and inverse-bank profiles for the individual moment systems. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 Gaussian Numerics.Native Inverse
open scoped ENNReal
noncomputable section

/-- All actual-law inputs of the individual source payment. This export
contains no norm, inverse-history, or numerical-profile premise. -/
theorem native_source_band_configured_profiles
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hpast : ∀ j<n,nativeInductionState M h j)
    (hstate : nativeInductionState M h n) (index : Fin 153)
    (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    let height := (nativeConfiguredSystem index).gap
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let T := fun ω => modelTraceObservable n M.nu (Annealed.sigmaBar M n) (nativeSourceBandScalar n height t ω)
    let R := nativeSourceBandRemainder M n height t
    let P := fun ω => (nativeSourceBandHistory M n height t ω).toReal
    let D := fun ω => bankInverseTraceObservable n M.nu (Annealed.sigmaBar M n)
      M.nu_pos (Annealed.sigmaBar_characterization M n).1 (nativeSourceBandScalar n height t ω)
    AEStronglyMeasurable R μ ∧ AEStronglyMeasurable T μ ∧
    (∀ ω,0 ≤ R ω) ∧ (∀ ω,0 ≤ T ω) ∧
    eLpNorm' R 128 μ ≤ ENNReal.ofReal (nativeEps:ℝ) ∧
    eLpNorm' T 20 μ ≤ ENNReal.ofReal ((nativeOld height).x:ℝ) ∧
    eLpNorm' T 128 μ ≤ ENNReal.ofReal ((nativeOld height).f:ℝ) ∧
    (∀ᵐ ω ∂μ,0 ≤ P ω ∧ D ω ≤ 2*P ω ∧ P ω ≤ (nativeB:ℝ)+R ω) := by
  let height := (nativeConfiguredSystem index).gap
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let T := fun ω => modelTraceObservable n M.nu (Annealed.sigmaBar M n) (nativeSourceBandScalar n height t ω)
  let R := nativeSourceBandRemainder M n height t
  have hs := native_source_band_history_rare_split M h hM hg n height hpast t ht.2
  have hT : AEStronglyMeasurable T μ :=
    ((modelTraceObservable_hasPolynomiallyBoundedC2Derivatives n M.nu (Annealed.sigmaBar M n)
      M.nu_pos (Annealed.sigmaBar_characterization M n).1).1.continuous.measurable.comp
        (native_source_band_scalar_measurable n height t)).aestronglyMeasurable
  have hT0 (ω) : 0 ≤ T ω := modelTraceObservable_nonneg n M.nu (Annealed.sigmaBar M n)
    M.nu_pos (Annealed.sigmaBar_characterization M n).1 _
  have hRnorm : eLpNorm' R 128 μ ≤ ENNReal.ofReal (nativeEps:ℝ) := by
    have hh := hs.2.2.2.1
    rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hs.2.1.aestronglyMeasurable] at hh
    simpa only [ENNReal.toReal_ofNat,nativeEps,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] using hh
  have hT20 := native_source_band_L20_le_configured_old M h hM hg n hpast hstate index t ht
  have hfull := native_source_band_full_response_L128 M h hM hg n height hpast t ht.2
  have hFmeas : AEStronglyMeasurable (fun ω => T ω+4) μ := hT.add aestronglyMeasurable_const
  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hFmeas] at hfull
  simp only [ENNReal.toReal_ofNat] at hfull
  have hmono : eLpNorm' T 128 μ ≤ eLpNorm' (fun ω => T ω+4) 128 μ := by
    apply eLpNorm'_mono_ae (by norm_num)
    filter_upwards [] with ω
    rw [Real.norm_of_nonneg (hT0 ω),Real.norm_of_nonneg (add_nonneg (hT0 ω) (by norm_num))]
    linarith
  have hparam := (heat_source_profiles_le_old M.gamma height M.shellPrefix.gamma_pos.le hg
    (by have hh := (heat_configured_gap_bounds index).2; dsimp [height]; omega)).2
  have hT128 := (hmono.trans hfull).trans (ENNReal.ofReal_le_ofReal hparam)
  refine ⟨hs.2.1.aestronglyMeasurable,hT,hs.2.2.1,hT0,hRnorm,hT20,hT128,?_⟩
  have hD := native_source_band_inverse_trace_ae_le M h hM hg n height hpast t ht.2
  filter_upwards [hD,hs.2.2.2.2] with ω hd hp
  exact ⟨ENNReal.toReal_nonneg,hd,by simpa only [nativeB,Rat.cast_div,Rat.cast_ofNat] using hp⟩

end
end ASDExplicitGamma.Native
