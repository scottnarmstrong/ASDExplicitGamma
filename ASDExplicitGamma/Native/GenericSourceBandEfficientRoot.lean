module

public import ASDExplicitGamma.Native.GenericSourceBandEfficientDerivative
public import ASDExplicitGamma.Native.GenericSourceBandRoot

/-! The native 0.62 corridor leaves a strict budget for the raw source profile. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic
open scoped ENNReal
noncomputable section

/-- Integrate the actual simultaneous raw moment derivative, including zero
moments and every partial time. -/
theorem native_source_band_root_efficient_increment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (height : ℕ) (hheight : 1 ≤ height)
    (hpast : ∀ j < n, nativeInductionState M h j) (hstate : nativeInductionState M h n)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    nativeSourceBandMoment M n height t^((20:ℝ)⁻¹)-
      nativeSourceBandMoment M n height 0^((20:ℝ)⁻¹) ≤
      t*nativeSourceRawMomentIncrement height (((4/5:ℝ)*nativeSourceRawShellVarianceCap M.gamma height))
        (nativeSourceFullResponseCap M.gamma height) := by
  let f := nativeSourceBandMoment M n height
  let c := nativeSourceRawMomentIncrement height (((4/5:ℝ)*nativeSourceRawShellVarianceCap M.gamma height))
    (nativeSourceFullResponseCap M.gamma height)
  have hg0 := M.shellPrefix.gamma_pos.le
  have hc : 0 ≤ c := by
    dsimp [c,nativeSourceRawMomentIncrement,nativeSourceRawShellVarianceCap,nativeSourceFullResponseCap,
      rawTraceFullResponseCap,nativeSourceK,nativeSourceM,nativeSourceQ,nativeSourceB128]
    positivity
  have hheat := native_source_band_moment_heat M h hM n height hheight
  have hcont : ContinuousOn f (Set.Icc (0:ℝ) 1) :=
    hheat.1.mono (fun _ ht => ht.1)
  have hdf : ∀ τ ∈ Set.Ioo (0:ℝ) 1, HasDerivAt f (deriv f τ) τ := by
    intro τ hτ
    have hd := hheat.2 τ hτ.1
    rw [hd.deriv]
    exact hd
  have hh := raw_p20_moment_root_sub_le_integral hcont
    (fun τ _ => native_source_band_moment_nonneg M n height τ) hdf
    (fun _ _ => hc)
    (integrableOn_const (C := c) (by rw [Real.volume_Icc]; norm_num))
    (fun τ hτ => native_source_band_moment_derivative_efficient M h hM hg n height hheight hpast hstate τ hτ)
    (s := 0) (t := t) (by norm_num) ht0 ht1
  simpa only [intervalIntegral.integral_const,sub_zero,smul_eq_mul] using hh


end
end ASDExplicitGamma.Native
