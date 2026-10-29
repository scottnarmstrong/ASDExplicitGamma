module

public import ASDExplicitGamma.Native.GenericSourceChildBandMeanPointwise
public import ASDExplicitGamma.Native.GenericSourceMeanDriftIntegral
public import ASDExplicitGamma.Native.GenericSourceMeanInterior

/-! The actual simultaneous mean drift with the literal rare reserve. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic
open scoped ENNReal
noncomputable section

/-- The refined-child scalar drift coefficient, with the stronger direct
old-frame local bank cap. -/
def nativeSourceChildMeanC : ℝ :=
  2*(65399707/10^9:ℝ)*(3683/2500)+(259713047/10^9:ℝ)*(3683/2500)^2

/-- The exact rare-product payment in the shifted mean drift. -/
def nativeSourceChildMeanR (height : ℕ) (epsilon x e : ℝ) : ℝ :=
  e*(2*(height:ℝ)*epsilon+
    (2*(65399707/10^9:ℝ)+2*(3683/2500)*(259713047/10^9))*(4*epsilon+epsilon*x)+
    (259713047/10^9:ℝ)*(4*epsilon^2+epsilon^2*x))

/-- Constant forcing in the literal refined-child mean inequality. -/
def nativeSourceChildMeanL (height : ℕ) (epsilon x e : ℝ) : ℝ :=
  e*(2*(height:ℝ)*(3683/2500)+4*nativeSourceChildMeanC)+
    nativeSourceChildMeanR height epsilon x e

/-- A simultaneous trace cap supplies exactly the scalar drift. Its
OLD positive split, inverse trace and every rare moment are discharged. -/
theorem native_source_child_band_mean_derivative
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (height : ℕ) (hheight : 1 ≤ height)
    (hpast : ∀ j < n, nativeInductionState M h j) (hstate : nativeInductionState M h n)
    (t : ℝ) (ht : t ∈ Set.Ioo (0:ℝ) 1) (x : ℝ) (hx : 0 ≤ x)
    (htrace : eLpNorm' (fun ω : Cutoff.CutoffSample 2 =>
      modelTraceObservable (n-1) M.nu (Annealed.sigmaBar M n) (nativeSourceChildBandScalar n height t ω))
      20 (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal x) :
    deriv (nativeSourceChildBandMean M n height) t ≤
      nativeSourceRawShellVarianceCap M.gamma height*nativeSourceChildMeanC*nativeSourceChildBandMean M n height t+
        nativeSourceChildMeanL height (3/10^46:ℝ) x (nativeSourceRawShellVarianceCap M.gamma height) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let σ : ℝ := Annealed.sigmaBar M n
  let X := nativeSourceChildBandScalar n height t
  let T := fun ω => modelTraceObservable (n-1) M.nu σ (X ω)
  let P := fun ω => (nativeSourceChildBandHistory M n height t ω).toReal
  let R := nativeSourceChildBandRemainder M n height t
  let D := fun ω => bankInverseTraceObservable (n-1) M.nu σ M.nu_pos
    (Annealed.sigmaBar_characterization M n).1 (X ω)
  let G := nativeSourceChildBandMeanGenerator M h n height t
  let b : ℝ := 3683/2500
  let epsilon : ℝ := 3/10^46
  let e := nativeSourceRawShellVarianceCap M.gamma height
  have hg0 := M.shellPrefix.gamma_pos.le
  have he : 0 ≤ e := by dsimp [e,nativeSourceRawShellVarianceCap]; positivity
  have hT0 (ω) : 0 ≤ T ω := modelTraceObservable_nonneg (n-1) M.nu σ M.nu_pos
    (Annealed.sigmaBar_characterization M n).1 _
  have hF0 (ω) : 0 ≤ T ω+4 := add_nonneg (hT0 ω) (by norm_num)
  have hΦ := modelTraceObservable_hasPolynomiallyBoundedC2Derivatives (n-1) M.nu σ
    M.nu_pos (Annealed.sigmaBar_characterization M n).1
  have hgrowth : HasPolynomialGrowth (modelTraceObservable (n-1) M.nu σ) := by
    obtain ⟨C,hC,d,hb,_,_⟩ := hΦ.2
    exact ⟨C,hC,d,hb⟩
  have hTmem : MemLp T (ENNReal.ofReal 20) μ :=
    native_source_child_band_test_memLp M h hM n height hheight _
      hΦ.1.continuous.measurable hgrowth t 20 (by norm_num)
  have hrare := native_source_child_band_history_rare_split M h hM hg n height hpast t ht.2.le
  have hRm : AEStronglyMeasurable R μ := hrare.2.1.aestronglyMeasurable
  have hR0 (ω) : 0 ≤ R ω := hrare.2.2.1 ω
  have hRcap : eLpNorm' R 128 μ ≤ ENNReal.ofReal epsilon := by
    have hh := hrare.2.2.2.1
    rw [eLpNorm_eq_eLpNorm' (by norm_num : (128:ℝ≥0∞)≠0)
      (by norm_num : (128:ℝ≥0∞)≠⊤) hRm] at hh
    exact hh
  have hpoint : ∀ᵐ ω ∂μ, G ω ≤ e*(2*(height:ℝ)*(b+R ω)+
      2*(65399707/10^9:ℝ)*((b+R ω)*(T ω+4))+(259713047/10^9:ℝ)*((b+R ω)^2*(T ω+4))) := by
    filter_upwards [native_source_child_band_mean_generator_ae_le M h hM hg n height hpast hstate t ht.2.le,
      native_source_child_band_inverse_trace_ae_le M h hM hg n height hpast t ht.2.le,
      hrare.2.2.2.2] with ω hG hD hP
    have hP0 : 0 ≤ P ω := ENNReal.toReal_nonneg
    have hB0 : 0 ≤ b+R ω := add_nonneg (by norm_num [b]) (hR0 ω)
    have h1 := mul_le_mul_of_nonneg_left
      (hD.trans (mul_le_mul_of_nonneg_left hP (by norm_num : (0:ℝ)≤2)))
      (Nat.cast_nonneg height : (0:ℝ)≤height)
    have h2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hP (hF0 ω))
      (show (0:ℝ)≤2*(65399707/10^9) by norm_num)
    have h3 := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hP0 hP 2) (hF0 ω))
      (show (0:ℝ)≤259713047/10^9 by norm_num)
    have hh := mul_le_mul_of_nonneg_left (add_le_add (add_le_add h1 h2) h3) he
    have hbound := hG.trans hh
    convert hbound using 1
    ring
  have hi := native_source_mean_drift_integral μ T R G
    (hTmem.integrable (by norm_num : (1:ℝ≥0∞)≤ENNReal.ofReal (20:ℝ)))
    (native_source_child_band_mean_generator_integrable M h hM n height hheight t)
    hRm hT0 hR0 b epsilon x e height (65399707/10^9) (259713047/10^9)
    (by norm_num [b]) (by positivity) hx he (by positivity) (by norm_num) (by norm_num)
    hRcap htrace hpoint
  have hd := (native_source_child_band_mean_heat_generator M h hM n height hheight).2 t ht.1
  rw [hd.deriv]
  convert hi using 1
  dsimp [nativeSourceChildMeanC,nativeSourceChildMeanL,nativeSourceChildMeanR,
    nativeSourceB128,nativeSourceChildBandMean,T,X,σ,μ,e,b,epsilon]
  ring

end
end ASDExplicitGamma.Native
