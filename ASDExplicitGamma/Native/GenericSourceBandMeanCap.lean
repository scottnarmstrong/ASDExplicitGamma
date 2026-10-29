module

public import ASDExplicitGamma.Native.GenericSourceBandMeanDerivative

/-! The exact exponential/phi1 mean bound on the simultaneous source law. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic
noncomputable section

/-- Integrate the actual source drift from the native ordinary mean, with
continuity at zero and the full positive rare reserve. -/
theorem native_source_band_mean_cap_of_uniform_trace
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (height : ℕ) (hheight : 1 ≤ height)
    (hpast : ∀ j < n, nativeInductionState M h j) (hstate : nativeInductionState M h n)
    (x : ℝ) (hx : 0 ≤ x) (htrace : nativeSourceBandUniformCap M n height x) :
    nativeSourceBandMean M n height 1 ≤
      ((3/50:ℝ)*theta M)*Real.exp (nativeSourceRawShellVarianceCap M.gamma height*nativeSourceMeanC)+
        nativeSourceMeanL height (3/10^46:ℝ) x (nativeSourceRawShellVarianceCap M.gamma height)*
          nativeSourcePhiOne (nativeSourceRawShellVarianceCap M.gamma height*nativeSourceMeanC) := by
  let f := nativeSourceBandMean M n height
  let df := fun t => ∫ ω, nativeSourceBandMeanGenerator M h n height t ω
    ∂(Cutoff.cutoffSampleLaw M).toMeasure
  let e := nativeSourceRawShellVarianceCap M.gamma height
  let c := e*nativeSourceMeanC
  let L := nativeSourceMeanL height (3/10^46:ℝ) x e
  have he : 0 < e := by
    have hg0 := M.shellPrefix.gamma_pos
    dsimp [e,nativeSourceRawShellVarianceCap]
    positivity
  have hc : 0 < c := mul_pos he (by norm_num [nativeSourceMeanC,nativeSourceK,nativeSourceM,nativeSourceB128])
  have hheat := native_source_band_mean_heat_generator M h hM n height hheight
  apply native_source_scalar_mean_of_interior_derivative f df _ c L hc
    (hheat.1.mono (fun _ ht => ht.1))
    (fun t ht => hheat.2 t ht.1) (native_source_band_mean_zero_le M h n height hstate)
  intro t ht
  have hd := hheat.2 t ht.1
  dsimp only [df]
  rw [←hd.deriv]
  exact native_source_band_mean_derivative M h hM hg n height hheight hpast hstate t ht x hx
    (htrace t ⟨ht.1.le,ht.2.le⟩)

end
end ASDExplicitGamma.Native
