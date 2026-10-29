module

public import ASDExplicitGamma.Native.GenericSourceBandMeanCap
public import ASDExplicitGamma.Native.GenericSourceMeanMonotone
public import ASDExplicitGamma.Native.GenericSourceRawTailProfile

/-! The literal finite source profile, now bounding the actual simultaneous
laws after all four heat refinements. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic
noncomputable section

/-- The exact rational four-pass profile bounds the actual simultaneous source
laws on the finite prefix; all random-law premises are discharged. -/
theorem native_source_band_generic_individual_profile
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hpast : ∀ j < n, nativeInductionState M h j)
    (hstate : nativeInductionState M h n) (height : ℕ) (hheight : 1 ≤ height) (hh : height ≤ 1332) :
    nativeSourceBandUniformCap M n height
      (nativeSourceGenericIndividualProfile M.gamma (theta M) height) := by
  have hg0 := M.shellPrefix.gamma_pos.le
  have hg' : M.gamma ≤ 17/50000 := hg
  have htheta : 0 ≤ theta M := div_nonneg hg0 (by norm_num [gammaZero])
  have ha : 0 ≤ (3/50:ℝ)*theta M := mul_nonneg (by norm_num) htheta
  have he : 0 ≤ nativeSourceRawShellVarianceCap M.gamma height := by
    unfold nativeSourceRawShellVarianceCap
    positivity
  have hecap := native_source_true_variance_le_generic M.gamma height hg0 hg' (by omega)
  have he0 : 0 ≤ nativeSourceGenericVarianceCap M.gamma height :=
    he.trans hecap
  have hf : 0 ≤ nativeSourceFullResponseCap M.gamma height := by
    unfold nativeSourceFullResponseCap rawTraceFullResponseCap
    positivity
  have hfcap := native_source_generic_full_response_cap_le_bank M.gamma height hg0 hg' hh
  have hf0 : 0 ≤ nativeSourceGenericFullResponseCap M.gamma height := hf.trans hfcap
  have hprofile := native_source_generic_individual_degree_split height
    (theta := 1) (by norm_num) (by norm_num) ha ha (by simp) he he0
    (by simpa only [one_mul] using hecap) hf hf0 hfcap 4
  simp only [one_mul] at hprofile
  intro t ht
  exact (native_source_band_four_pass M h hM hg n hpast hstate height hheight t ht).trans
    (ENNReal.ofReal_le_ofReal hprofile)

/-- The actual unframed source mean has the exact finite rational clock and
four-pass trace cap. No frame-restoration estimate is assumed. -/
theorem native_source_band_mean_rational_solution
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hpast : ∀ j < n, nativeInductionState M h j)
    (hstate : nativeInductionState M h n) (height : ℕ) (hheight : 1 ≤ height) (hh : height ≤ 1332) :
    let a := (3/50:ℝ)*theta M
    let e := nativeSourceGenericVarianceCap M.gamma height
    let x := nativeSourceGenericIndividualProfile M.gamma (theta M) height
    nativeSourceBandMean M n height 1 ≤
      a*Real.exp (e*nativeSourceMeanC)+nativeSourceMeanL height (3/10^46:ℝ) x e*
        nativeSourcePhiOne (e*nativeSourceMeanC) := by
  dsimp only
  have hg0 := M.shellPrefix.gamma_pos.le
  have ht0 : 0 ≤ theta M := div_nonneg hg0 (by norm_num [gammaZero])
  have hx := native_source_generic_individual_profile_nonneg M.gamma (theta M) height hg0 ht0 hg hh
  have htrace := native_source_band_generic_individual_profile M h hM hg n hpast hstate height hheight hh
  have hbound := native_source_band_mean_cap_of_uniform_trace M h hM hg n height hheight hpast hstate _ hx htrace
  have he : 0 ≤ nativeSourceRawShellVarianceCap M.gamma height := by dsimp [nativeSourceRawShellVarianceCap]; positivity
  exact hbound.trans (native_source_mean_solution_mono height _ _ _ _ _ _ _
    (mul_nonneg (by norm_num) ht0) le_rfl (by positivity) hx le_rfl he
    (native_source_true_variance_le_generic M.gamma height hg0 hg (by omega)))

end
end ASDExplicitGamma.Native
