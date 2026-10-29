module

public import ASDExplicitGamma.Native.GenericSourceBandCoefficientW
public import ASDExplicitGamma.Inverse.FullResponseCoefficientTransport
public import ASDExplicitGamma.Inverse.BankObservers
public import ASDExplicitGamma.Model.Cutoff
public import ASDExplicitGamma.Inverse.PureFluxGeneratorBankLaw
public import ASDExplicitGamma.Inverse.BankOnePassMeanActual
public import ASDExplicitGamma.Gaussian.ShellBracket

public import ASDExplicitGamma.Native.NativeBandWeight

/-! The actual local and full128 banks along simultaneous source-band heat. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic ASDExplicitGamma.Response
open ASDExplicitGamma.Variational
open scoped ENNReal
noncomputable section

variable {W : NativeAmp}

/-- Actual extended local inverse history on the simultaneous finite band. -/
def nativeSourceBandHistory_W (W : NativeAmp) (M : ABKModel 2) (n : ℤ) (height : ℕ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) : ℝ≥0∞ :=
  bankFiniteRootHistoryMax (bankLocalRoots (originCube 2 n) 5) M n (n+(height:ℤ))
    (nativeAttW W t) ω

/-- The genuine local positive remainder on that same source-band law. -/
def nativeSourceBandRemainder_W (W : NativeAmp) (M : ABKModel 2) (n : ℤ) (height : ℕ) (t : ℝ) :
    Cutoff.CutoffSample 2 → ℝ :=
  inverseBankPopulationRemainder .localInverse (bankLocalRoots (originCube 2 n) 5)
    M n (n+(height:ℤ)) (nativeAttW W t)

/-- All local-bank estimates, including the small positive reserve and
extended history finiteness, hold on every simultaneous source-band law. -/
theorem native_source_band_local_bank_W
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (height : ℕ)
    (hpast : ∀ j < n, nativeInductionState M h j) (t : ℝ) (ht1 : t ≤ 1) :
    InverseBankConclusion M .localInverse (bankLocalRoots (originCube 2 n) 5)
      n (n+(height:ℤ)) (nativeAttW W t) := by
  have hgeom := bank_local_roots_geometry (originCube 2 n) 5 (by norm_num)
  have hmean := (bank_inverse_mean_inputs_of_states M h hM hg n hpast).2
  exact local_inverse_bank M h hM hg _ n (n+(height:ℤ)) (by omega) _
    (fun k _ => nativeAttW_mem W ht1 k)
    hgeom.1 hgeom.2 hpast hmean

/-- The actual local source history has a finite positive split, with the
same OLD `b` and genuine `3e-46` remainder as the sequential source path. -/
theorem native_source_band_history_rare_split_W
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (height : ℕ)
    (hpast : ∀ j < n, nativeInductionState M h j) (t : ℝ) (ht1 : t ≤ 1) :
    (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure, nativeSourceBandHistory_W W M n height t ω < ⊤) ∧
    Measurable (nativeSourceBandRemainder_W W M n height t) ∧
    (∀ ω, 0 ≤ nativeSourceBandRemainder_W W M n height t ω) ∧
    eLpNorm (nativeSourceBandRemainder_W W M n height t) 128 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (3/10^46:ℝ) ∧
    (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      (nativeSourceBandHistory_W W M n height t ω).toReal ≤
        (3683/2500:ℝ)+nativeSourceBandRemainder_W W M n height t ω) := by
  have hb := native_source_band_local_bank_W (W := W) M h hM hg n height hpast t ht1
  refine ⟨hb.history_finite,hb.remainder_measurable,hb.remainder_nonneg,?_,?_⟩
  · simpa only [nativeSourceBandRemainder_W,inverseBankReserve,
      Rat.cast_div,Rat.cast_ofNat,Rat.cast_pow] using hb.remainder_L128
  · filter_upwards [hb.history_le] with ω hω
    have hR := hb.remainder_nonneg ω
    have hcap : (0:ℝ) ≤ (inverseBankCap .localInverse:ℝ) := by norm_num [inverseBankCap]
    rw [←ENNReal.ofReal_add hcap hR] at hω
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hω
    rw [ENNReal.toReal_ofReal (add_nonneg hcap hR)] at hh
    simpa only [nativeSourceBandHistory_W,nativeSourceBandRemainder_W,inverseBankCap,
      Rat.cast_div,Rat.cast_ofNat] using hh

/-- The actual simultaneous-band trace is the exact bank attenuation
observable, with no truncation or change of the fixed true frame. -/
theorem native_source_band_full_response_identity_W (M : ABKModel 2) (n : ℤ) (height : ℕ)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    modelTraceObservable n M.nu (Annealed.sigmaBar M n) (nativeSourceBandScalar_W W n height t ω)+4 =
      nativeSourceFullResponseTrace M (originCube 2 n) n (n+(height:ℤ)) (nativeAttW W t) ω := by
  have hae : responsePlanarCoefficientField M.nu
      (ContinuousMap.linearIsometryBoundedOfCompact (closure (cubeSet (originCube 2 n))) ℝ ℝ
        (nativeSourceBandScalar_W W n height t ω)) =ᵐ[volume.restrict (cubeSet (originCube 2 n))]
      attenuatedCoefficient M n (n+(height:ℤ)) (nativeAttW W t) ω :=
    (ae_restrict_mem (μ := volume) (measurableSet_cubeSet (originCube 2 n))).mono
      (fun x hx => native_source_band_coefficient_on_cube_W M n height t ω x hx)
  unfold modelTraceObservable
  rw [traceDefect_eq_framedTrace,coarseBlockMatrix_congr_of_ae_eq hae]
  unfold nativeSourceFullResponseTrace
  ring

/-- The actual full128 response estimate along the whole simultaneous band. -/
theorem native_source_band_full_response_L128_W
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (height : ℕ)
    (hpast : ∀ j < n, nativeInductionState M h j) (t : ℝ) (ht1 : t ≤ 1) :
    eLpNorm (fun ω : Cutoff.CutoffSample 2 =>
      modelTraceObservable n M.nu (Annealed.sigmaBar M n) (nativeSourceBandScalar_W W n height t ω)+4)
      128 (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (rawTraceFullResponseCap M.gamma height) := by
  have hh := native_source_full_response_L128_actual M h hM hg (originCube 2 n) height hpast
    (nativeAttW W t) (fun k _ => nativeAttW_mem W ht1 k)
  have hscale : (originCube 2 n).scale=n := rfl
  rw [hscale] at hh
  have he : (fun ω : Cutoff.CutoffSample 2 =>
      modelTraceObservable n M.nu (Annealed.sigmaBar M n) (nativeSourceBandScalar_W W n height t ω)+4) =
      nativeSourceFullResponseTrace M (originCube 2 n) n (n+(height:ℤ)) (nativeAttW W t) :=
    funext (native_source_band_full_response_identity_W M n height t)
  rw [he]
  simpa only [show ENNReal.ofReal (128:ℝ)=(128:ℝ≥0∞) by norm_num] using hh

end
end ASDExplicitGamma.Native
