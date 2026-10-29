module

public import ASDExplicitGamma.Native.GenericSourceBandMeanHeat
public import ASDExplicitGamma.Native.GenericSourceBandPasses
public import ASDExplicitGamma.Native.GenericSourceMeanDriftIntegral
public import ASDExplicitGamma.Native.GenericSourceMeanInterior

/-! The actual simultaneous mean drift with the literal rare reserve. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic
open scoped ENNReal
noncomputable section

/-- A simultaneous trace cap supplies exactly the scalar drift. Its
OLD positive split, inverse trace and every rare moment are discharged. -/
theorem native_source_band_mean_derivative
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (height : ℕ) (hheight : 1 ≤ height)
    (hpast : ∀ j < n, nativeInductionState M h j) (hstate : nativeInductionState M h n)
    (t : ℝ) (ht : t ∈ Set.Ioo (0:ℝ) 1) (x : ℝ) (hx : 0 ≤ x)
    (htrace : eLpNorm' (fun ω : Cutoff.CutoffSample 2 =>
      modelTraceObservable n M.nu (Annealed.sigmaBar M n) (nativeSourceBandScalar n height t ω))
      20 (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal x) :
    deriv (nativeSourceBandMean M n height) t ≤
      nativeSourceRawShellVarianceCap M.gamma height*nativeSourceMeanC*nativeSourceBandMean M n height t+
        nativeSourceMeanL height (3/10^46:ℝ) x (nativeSourceRawShellVarianceCap M.gamma height) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let σ : ℝ := Annealed.sigmaBar M n
  let X := nativeSourceBandScalar n height t
  let T := fun ω => modelTraceObservable n M.nu σ (X ω)
  let P := fun ω => (nativeSourceBandHistory M n height t ω).toReal
  let R := nativeSourceBandRemainder M n height t
  let D := fun ω => bankInverseTraceObservable n M.nu σ M.nu_pos
    (Annealed.sigmaBar_characterization M n).1 (X ω)
  let G := nativeSourceBandMeanGenerator M h n height t
  let b : ℝ := 3683/2500
  let epsilon : ℝ := 3/10^46
  let e := nativeSourceRawShellVarianceCap M.gamma height
  have hg0 := M.shellPrefix.gamma_pos.le
  have he : 0 ≤ e := by dsimp [e,nativeSourceRawShellVarianceCap]; positivity
  have hT0 (ω) : 0 ≤ T ω := modelTraceObservable_nonneg n M.nu σ M.nu_pos
    (Annealed.sigmaBar_characterization M n).1 _
  have hF0 (ω) : 0 ≤ T ω+4 := add_nonneg (hT0 ω) (by norm_num)
  have hTmem : MemLp T (ENNReal.ofReal 20) μ :=
    (native_source_band_raw_factors M h hM hg n height hpast t ht.2.le).1
  have hrare := native_source_band_history_rare_split M h hM hg n height hpast t ht.2.le
  have hRm : AEStronglyMeasurable R μ := hrare.2.1.aestronglyMeasurable
  have hR0 (ω) : 0 ≤ R ω := hrare.2.2.1 ω
  have hRcap : eLpNorm' R 128 μ ≤ ENNReal.ofReal epsilon := by
    have hh := hrare.2.2.2.1
    rw [eLpNorm_eq_eLpNorm' (by norm_num : (128:ℝ≥0∞)≠0)
      (by norm_num : (128:ℝ≥0∞)≠⊤) hRm] at hh
    exact hh
  have hpoint : ∀ᵐ ω ∂μ, G ω ≤ e*(2*(height:ℝ)*(b+R ω)+
      2*(521/1000:ℝ)*((b+R ω)*(T ω+4))+(1975/1000:ℝ)*((b+R ω)^2*(T ω+4))) := by
    filter_upwards [native_source_band_mean_generator_ae_le M h hM hg n height hpast hstate t ht.2.le,
      native_source_band_inverse_trace_ae_le M h hM hg n height hpast t ht.2.le,
      hrare.2.2.2.2] with ω hG hD hP
    have hP0 : 0 ≤ P ω := ENNReal.toReal_nonneg
    have hB0 : 0 ≤ b+R ω := add_nonneg (by norm_num [b]) (hR0 ω)
    have h1 := mul_le_mul_of_nonneg_left
      (hD.trans (mul_le_mul_of_nonneg_left hP (by norm_num : (0:ℝ)≤2)))
      (Nat.cast_nonneg height : (0:ℝ)≤height)
    have h2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hP (hF0 ω))
      (show (0:ℝ)≤2*(521/1000) by norm_num)
    have h3 := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hP0 hP 2) (hF0 ω))
      (show (0:ℝ)≤1975/1000 by norm_num)
    have hh := mul_le_mul_of_nonneg_left (add_le_add (add_le_add h1 h2) h3) he
    have hbound := hG.trans hh
    convert hbound using 1
    ring
  have hi := native_source_mean_drift_integral μ T R G
    (hTmem.integrable (by norm_num : (1:ℝ≥0∞)≤ENNReal.ofReal (20:ℝ)))
    (native_source_band_mean_generator_integrable M h hM n height hheight t)
    hRm hT0 hR0 b epsilon x e height (521/1000) (1975/1000)
    (by norm_num [b]) (by positivity) hx he (by positivity) (by norm_num) (by norm_num)
    hRcap htrace hpoint
  have hd := (native_source_band_mean_heat_generator M h hM n height hheight).2 t ht.1
  rw [hd.deriv]
  convert hi using 1
  dsimp [nativeSourceMeanC,nativeSourceMeanL,nativeSourceMeanR,nativeSourceK,nativeSourceM,
    nativeSourceB128,nativeSourceBandMean,T,X,σ,μ,e,b,epsilon]
  ring

end
end ASDExplicitGamma.Native
