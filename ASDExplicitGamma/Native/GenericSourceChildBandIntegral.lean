module

public import ASDExplicitGamma.Native.GenericSourceChildBandPowerMoments
public import ASDExplicitGamma.Inverse.SourceP20LinearHolder

/-! The simultaneous actual p20 generator integrated with its three
separate norm factors, ready for either raw or finite-pass caps. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic
open scoped ENNReal
noncomputable section

theorem native_source_child_band_power_integral_norm_row
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (height : ℕ) (hheight : 1 ≤ height)
    (hpast : ∀ j < n, nativeInductionState M h j) (hstate : nativeInductionState M h n)
    (t : ℝ) (ht1 : t ≤ 1) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let σ : ℝ := Annealed.sigmaBar M n
    let X := nativeSourceChildBandScalar n height t
    let T := fun ω => modelTraceObservable (n-1) M.nu σ (X ω)
    let F := fun ω => T ω+4
    let P := fun ω => (nativeSourceChildBandHistory M n height t ω).toReal
    let D := fun ω => bankInverseTraceObservable (n-1) M.nu σ M.nu_pos
      (Annealed.sigmaBar_characterization M n).1 (X ω)
    (∫ ω, nativeSourceChildBandPowerGenerator M h n height t ω ∂μ) ≤
      20*(∫ ω, T ω^(20:ℝ) ∂μ)^((19:ℝ)/20)*
        (nativeSourceRawShellVarianceCap M.gamma height*
          ((39*(height:ℝ)+38*(65399707/10^9:ℝ))*positiveLpNorm μ 20 D+
            2*(65399707/10^9:ℝ)*positiveLpNorm μ 20 (fun ω => P ω*F ω)+
            ((259713047/10^9:ℝ)+38*((259713047/10^9:ℝ)+(65399707/10^9:ℝ)))*positiveLpNorm μ 20 (fun ω => (P ω)^2*F ω))) := by
  dsimp only
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let σ : ℝ := Annealed.sigmaBar M n
  let X := nativeSourceChildBandScalar n height t
  let T := fun ω => modelTraceObservable (n-1) M.nu σ (X ω)
  let F := fun ω => T ω+4
  let P := fun ω => (nativeSourceChildBandHistory M n height t ω).toReal
  let D := fun ω => bankInverseTraceObservable (n-1) M.nu σ M.nu_pos
    (Annealed.sigmaBar_characterization M n).1 (X ω)
  let e := nativeSourceRawShellVarianceCap M.gamma height
  let G := nativeSourceChildBandPowerGenerator M h n height t
  let Fs : Fin 3 → Cutoff.CutoffSample 2 → ℝ := ![D,fun ω => P ω*F ω,fun ω => (P ω)^2*F ω]
  let a : Fin 3 → ℝ := ![20*e*(39*(height:ℝ)+38*(65399707/10^9:ℝ)),
    20*e*(2*(65399707/10^9:ℝ)),20*e*((259713047/10^9:ℝ)+38*((259713047/10^9:ℝ)+(65399707/10^9:ℝ)))]
  have hg0 := M.shellPrefix.gamma_pos.le
  have he : 0 ≤ e := by dsimp [e,nativeSourceRawShellVarianceCap]; positivity
  have hT0 (ω) : 0 ≤ T ω := modelTraceObservable_nonneg (n-1) M.nu σ M.nu_pos
    (Annealed.sigmaBar_characterization M n).1 _
  have hD0 (ω) : 0 ≤ D ω := native_source_model_inverse_trace_nonneg (n-1) M.nu σ M.nu_pos
    (Annealed.sigmaBar_characterization M n).1 _
  have hF0 (ω) : 0 ≤ F ω := add_nonneg (hT0 ω) (by norm_num)
  have hP0 (ω) : 0 ≤ P ω := ENNReal.toReal_nonneg
  have hdata := native_source_child_band_raw_factors M h hM hg n height hpast t ht1
  have hFs (j : Fin 3) : MemLp (Fs j) (ENNReal.ofReal 20) μ := by
    fin_cases j
    · exact hdata.2.1
    · exact hdata.2.2.1
    · exact hdata.2.2.2.1
  have hFs0 (j : Fin 3) (ω) : 0 ≤ Fs j ω := by
    fin_cases j
    · exact hD0 ω
    · exact mul_nonneg (hP0 ω) (hF0 ω)
    · exact mul_nonneg (sq_nonneg (P ω)) (hF0 ω)
  have ha (j : Fin 3) : 0 ≤ a j := by fin_cases j <;> dsimp [a] <;> positivity
  have hpoint : ∀ᵐ ω ∂μ, G ω ≤ ∑ j : Fin 3, a j*(T ω^(19:ℝ)*Fs j ω) := by
    filter_upwards [native_source_child_band_power_generator_ae_le M h hM hg n height hpast hstate t ht1]
      with ω hω
    convert hω using 1
    norm_num [Fs,a,Fin.sum_univ_succ]
    ring
  have hh := source_p20_integral_linear_factors μ T G Fs a hT0 hFs0 ha hdata.1 hFs
    (native_source_child_band_power_generator_integrable M h hM n height hheight t) hpoint
  convert hh using 1
  norm_num [Fs,a,Fin.sum_univ_succ]
  ring

end
end ASDExplicitGamma.Native
