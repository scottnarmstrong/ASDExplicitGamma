module

public import ASDExplicitGamma.Native.GenericSourceBandCoefficient
public import ASDExplicitGamma.Inverse.FullResponseCoefficientTransport
public import ASDExplicitGamma.Inverse.BankObservers
public import ASDExplicitGamma.Model.Cutoff
public import ASDExplicitGamma.Inverse.PureFluxGeneratorBankLaw
public import ASDExplicitGamma.Inverse.BankOnePassMeanActual
public import ASDExplicitGamma.Gaussian.ShellBracket

/-! The actual local and full128 banks along simultaneous source-band heat. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic ASDExplicitGamma.Response
open ASDExplicitGamma.Variational
open scoped ENNReal
noncomputable section

/-- Actual extended local inverse history on the simultaneous finite band. -/
def nativeSourceBandHistory (M : ABKModel 2) (n : ℤ) (height : ℕ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) : ℝ≥0∞ :=
  bankFiniteRootHistoryMax (bankLocalRoots (originCube 2 n) 5) M n (n+(height:ℤ))
    (fun _ => Real.sqrt t) ω

/-- The genuine local positive remainder on that same source-band law. -/
def nativeSourceBandRemainder (M : ABKModel 2) (n : ℤ) (height : ℕ) (t : ℝ) :
    Cutoff.CutoffSample 2 → ℝ :=
  inverseBankPopulationRemainder .localInverse (bankLocalRoots (originCube 2 n) 5)
    M n (n+(height:ℤ)) (fun _ => Real.sqrt t)

/-- All local-bank estimates, including the small positive reserve and
extended history finiteness, hold on every simultaneous source-band law. -/
theorem native_source_band_local_bank
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (height : ℕ)
    (hpast : ∀ j < n, nativeInductionState M h j) (t : ℝ) (ht1 : t ≤ 1) :
    InverseBankConclusion M .localInverse (bankLocalRoots (originCube 2 n) 5)
      n (n+(height:ℤ)) (fun _ => Real.sqrt t) := by
  have hgeom := bank_local_roots_geometry (originCube 2 n) 5 (by norm_num)
  have hmean := (bank_inverse_mean_inputs_of_states M h hM hg n hpast).2
  exact local_inverse_bank M h hM hg _ n (n+(height:ℤ)) (by omega) _
    (fun _ _ => ⟨Real.sqrt_nonneg t,Real.sqrt_le_one.mpr ht1⟩)
    hgeom.1 hgeom.2 hpast hmean

/-- The actual local source history has a finite positive split, with the
same OLD `b` and genuine `3e-46` remainder as the sequential source path. -/
theorem native_source_band_history_rare_split
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (height : ℕ)
    (hpast : ∀ j < n, nativeInductionState M h j) (t : ℝ) (ht1 : t ≤ 1) :
    (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure, nativeSourceBandHistory M n height t ω < ⊤) ∧
    Measurable (nativeSourceBandRemainder M n height t) ∧
    (∀ ω, 0 ≤ nativeSourceBandRemainder M n height t ω) ∧
    eLpNorm (nativeSourceBandRemainder M n height t) 128 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (3/10^46:ℝ) ∧
    (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      (nativeSourceBandHistory M n height t ω).toReal ≤
        (3683/2500:ℝ)+nativeSourceBandRemainder M n height t ω) := by
  have hb := native_source_band_local_bank M h hM hg n height hpast t ht1
  refine ⟨hb.history_finite,hb.remainder_measurable,hb.remainder_nonneg,?_,?_⟩
  · simpa only [nativeSourceBandRemainder,inverseBankReserve,
      Rat.cast_div,Rat.cast_ofNat,Rat.cast_pow] using hb.remainder_L128
  · filter_upwards [hb.history_le] with ω hω
    have hR := hb.remainder_nonneg ω
    have hcap : (0:ℝ) ≤ (inverseBankCap .localInverse:ℝ) := by norm_num [inverseBankCap]
    rw [←ENNReal.ofReal_add hcap hR] at hω
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hω
    rw [ENNReal.toReal_ofReal (add_nonneg hcap hR)] at hh
    simpa only [nativeSourceBandHistory,nativeSourceBandRemainder,inverseBankCap,
      Rat.cast_div,Rat.cast_ofNat] using hh

/-- The actual simultaneous-band trace is the exact bank attenuation
observable, with no truncation or change of the fixed true frame. -/
theorem native_source_band_full_response_identity (M : ABKModel 2) (n : ℤ) (height : ℕ)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    modelTraceObservable n M.nu (Annealed.sigmaBar M n) (nativeSourceBandScalar n height t ω)+4 =
      nativeSourceFullResponseTrace M (originCube 2 n) n (n+(height:ℤ)) (fun _ => Real.sqrt t) ω := by
  have hae : responsePlanarCoefficientField M.nu
      (ContinuousMap.linearIsometryBoundedOfCompact (closure (cubeSet (originCube 2 n))) ℝ ℝ
        (nativeSourceBandScalar n height t ω)) =ᵐ[volume.restrict (cubeSet (originCube 2 n))]
      attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) ω :=
    (ae_restrict_mem (μ := volume) (measurableSet_cubeSet (originCube 2 n))).mono
      (fun x hx => native_source_band_coefficient_on_cube M n height t ω x hx)
  unfold modelTraceObservable
  rw [traceDefect_eq_framedTrace,coarseBlockMatrix_congr_of_ae_eq hae]
  unfold nativeSourceFullResponseTrace
  ring

/-- The actual full128 response estimate along the whole simultaneous band. -/
theorem native_source_band_full_response_L128
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (height : ℕ)
    (hpast : ∀ j < n, nativeInductionState M h j) (t : ℝ) (ht1 : t ≤ 1) :
    eLpNorm (fun ω : Cutoff.CutoffSample 2 =>
      modelTraceObservable n M.nu (Annealed.sigmaBar M n) (nativeSourceBandScalar n height t ω)+4)
      128 (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (rawTraceFullResponseCap M.gamma height) := by
  have hh := native_source_full_response_L128_actual M h hM hg (originCube 2 n) height hpast
    (fun _ => Real.sqrt t) (fun _ _ => ⟨Real.sqrt_nonneg t,Real.sqrt_le_one.mpr ht1⟩)
  have hscale : (originCube 2 n).scale=n := rfl
  rw [hscale] at hh
  have he : (fun ω : Cutoff.CutoffSample 2 =>
      modelTraceObservable n M.nu (Annealed.sigmaBar M n) (nativeSourceBandScalar n height t ω)+4) =
      nativeSourceFullResponseTrace M (originCube 2 n) n (n+(height:ℤ)) (fun _ => Real.sqrt t) :=
    funext (native_source_band_full_response_identity M n height t)
  rw [he]
  simpa only [show ENNReal.ofReal (128:ℝ)=(128:ℝ≥0∞) by norm_num] using hh

end
end ASDExplicitGamma.Native
