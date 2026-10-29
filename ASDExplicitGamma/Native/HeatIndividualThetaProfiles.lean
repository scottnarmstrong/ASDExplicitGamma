module

public import ASDExplicitGamma.Native.HeatActualIndividualProfilesW
public import ASDExplicitGamma.Native.HeatStepThetaRow

/-! Theta-scaled actual profiles of the individual source law: the OLD `L^20` cap becomes
`θ · old.x`, the full-response `L^128` cap and the rare reserve stay fixed. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 Gaussian Numerics.Native Inverse
open scoped ENNReal
noncomputable section

variable {W : NativeAmp}

/-- The source shell variance is `θ`-proportional against the OLD slot. -/
theorem heat_source_variance_le_theta_old (gamma : ℝ) (height : ℕ)
    (hg0 : 0 ≤ gamma) (hg : gamma ≤ 17/50000) (hh : height ≤ 1332) :
    nativeSourceRawShellVarianceCap gamma height ≤
      (gamma / (17/50000 : ℝ)) * ((nativeOld height).e : ℝ) := by
  rw [heat_old_variance_endpoint]
  exact (native_source_true_variance_le_generic gamma height hg0 hg (by omega)).trans
    (native_source_generic_variance_cap_degree gamma (gamma / (17/50000 : ℝ)) height
      hg0 hg rfl (by omega))

/-- Theta-scaled OLD `L^20` profile of the actual individual source law. -/
theorem native_source_band_L20_le_configured_old_theta_W
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hpast : ∀ j<n,nativeInductionState M h j)
    (hstate : nativeInductionState M h n) (index : Fin 153) :
    nativeSourceBandUniformCap_W W M n (nativeConfiguredSystem index).gap
      (theta M * ((nativeOld (nativeConfiguredSystem index).gap).x : ℝ)) := by
  let height := (nativeConfiguredSystem index).gap
  let old := nativeOld height
  have hgap := heat_configured_gap_bounds index
  have hv := heat_configured_individual_old_valid index
  have hg0 := M.shellPrefix.gamma_pos.le
  obtain ⟨ht0, ht1⟩ := theta_pos_le_one M hg
  have he : 0 ≤ nativeSourceRawShellVarianceCap M.gamma height := by
    unfold nativeSourceRawShellVarianceCap
    positivity
  have hf : 0 ≤ nativeSourceFullResponseCap M.gamma height := by
    unfold nativeSourceFullResponseCap Inverse.rawTraceFullResponseCap
    positivity
  have hprofiles := heat_source_profiles_le_old M.gamma height hg0 hg (by dsimp [height]; omega)
  have hvar := heat_source_variance_le_theta_old M.gamma height hg0 hg
    (by dsimp [height]; omega)
  have hθ : M.gamma / (17/50000 : ℝ) = theta M := by
    unfold theta gammaZero; norm_num
  rw [hθ] at hvar
  have hdom := native_source_generic_individual_degree_split height
    (theta:=theta M) (a:=((3/50:ℝ)*theta M)) (a0:=(nativeA:ℝ))
    (e:=nativeSourceRawShellVarianceCap M.gamma height) (e0:=(old.e:ℝ))
    (f:=nativeSourceFullResponseCap M.gamma height) (f0:=(old.f:ℝ))
    ht0.le ht1 (by positivity) (by norm_num [nativeA])
    (by simp only [nativeA, Rat.cast_div, Rat.cast_ofNat]; nlinarith [ht0])
    he (by exact_mod_cast hv.1) hvar
    hf (by exact_mod_cast hv.2.2.1) hprofiles.2 4
  have hfull := hdom.trans (mul_le_mul_of_nonneg_left (heat_configured_old_real_profile index) ht0.le)
  have hcap := native_source_band_four_pass_W (W := W) M h hM hg n hpast hstate height hgap.1
  intro t ht
  exact (hcap t ht).trans (ENNReal.ofReal_le_ofReal hfull)

/-- All actual-law inputs of the individual source payment. This export
contains no norm, inverse-history, or numerical-profile premise. -/
theorem native_source_band_configured_profiles_theta_W
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hpast : ∀ j<n,nativeInductionState M h j)
    (hstate : nativeInductionState M h n) (index : Fin 153)
    (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    let height := (nativeConfiguredSystem index).gap
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let T := fun ω => modelTraceObservable n M.nu (Annealed.sigmaBar M n) (nativeSourceBandScalar_W W n height t ω)
    let R := nativeSourceBandRemainder_W W M n height t
    let P := fun ω => (nativeSourceBandHistory_W W M n height t ω).toReal
    let D := fun ω => bankInverseTraceObservable n M.nu (Annealed.sigmaBar M n)
      M.nu_pos (Annealed.sigmaBar_characterization M n).1 (nativeSourceBandScalar_W W n height t ω)
    AEStronglyMeasurable R μ ∧ AEStronglyMeasurable T μ ∧
    (∀ ω,0 ≤ R ω) ∧ (∀ ω,0 ≤ T ω) ∧
    eLpNorm' R 128 μ ≤ ENNReal.ofReal (nativeEps:ℝ) ∧
    eLpNorm' T 20 μ ≤ ENNReal.ofReal (theta M * ((nativeOld height).x:ℝ)) ∧
    eLpNorm' T 128 μ ≤ ENNReal.ofReal ((nativeOld height).f:ℝ) ∧
    (∀ᵐ ω ∂μ,0 ≤ P ω ∧ D ω ≤ 2*P ω ∧ P ω ≤ (nativeB:ℝ)+R ω) := by
  let height := (nativeConfiguredSystem index).gap
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let T := fun ω => modelTraceObservable n M.nu (Annealed.sigmaBar M n) (nativeSourceBandScalar_W W n height t ω)
  let R := nativeSourceBandRemainder_W W M n height t
  have hs := native_source_band_history_rare_split_W (W := W) M h hM hg n height hpast t ht.2
  have hT : AEStronglyMeasurable T μ :=
    ((modelTraceObservable_hasPolynomiallyBoundedC2Derivatives n M.nu (Annealed.sigmaBar M n)
      M.nu_pos (Annealed.sigmaBar_characterization M n).1).1.continuous.measurable.comp
        (native_source_band_scalar_measurable_W n height t)).aestronglyMeasurable
  have hT0 (ω) : 0 ≤ T ω := modelTraceObservable_nonneg n M.nu (Annealed.sigmaBar M n)
    M.nu_pos (Annealed.sigmaBar_characterization M n).1 _
  have hRnorm : eLpNorm' R 128 μ ≤ ENNReal.ofReal (nativeEps:ℝ) := by
    have hh := hs.2.2.2.1
    rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hs.2.1.aestronglyMeasurable] at hh
    simpa only [ENNReal.toReal_ofNat,nativeEps,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] using hh
  have hT20 := native_source_band_L20_le_configured_old_theta_W (W := W) M h hM hg n hpast hstate index t ht
  have hfull := native_source_band_full_response_L128_W (W := W) M h hM hg n height hpast t ht.2
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
  have hD := native_source_band_inverse_trace_ae_le_W (W := W) M h hM hg n height hpast t ht.2
  filter_upwards [hD,hs.2.2.2.2] with ω hd hp
  exact ⟨ENNReal.toReal_nonneg,hd,by simpa only [nativeB,Rat.cast_div,Rat.cast_ofNat] using hp⟩

end
end ASDExplicitGamma.Native
