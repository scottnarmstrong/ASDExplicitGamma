module

public import ASDExplicitGamma.Native.HeatConfiguredOldProfiles
public import ASDExplicitGamma.Native.GenericSourceBandPassesW

public import ASDExplicitGamma.Native.NativeBandWeight

/-! The actual individual source law obeys each selected OLD L20 input. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 Gaussian Numerics.Native
noncomputable section

variable {W : NativeAmp}

/-- Actual OLD L20 profiles for every selected individual solve. All four
refinements and their checked radicals are proved inside this export; there
is no trace norm or cooperative generator estimate among its premises. -/
theorem native_source_band_L20_le_configured_old_W
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hpast : ∀ j<n,nativeInductionState M h j)
    (hstate : nativeInductionState M h n) (index : Fin 153) :
    nativeSourceBandUniformCap_W W M n (nativeConfiguredSystem index).gap
      (nativeOld (nativeConfiguredSystem index).gap).x := by
  let height := (nativeConfiguredSystem index).gap
  let old := nativeOld height
  have hgap := heat_configured_gap_bounds index
  have hv := heat_configured_individual_old_valid index
  have hg0 := M.shellPrefix.gamma_pos.le
  have ht0 : 0 ≤ theta M := div_nonneg hg0 (by norm_num [gammaZero])
  have ht1 : theta M ≤ 1 := (div_le_one₀ (by norm_num [gammaZero])).2 hg
  have he : 0 ≤ nativeSourceRawShellVarianceCap M.gamma height := by
    unfold nativeSourceRawShellVarianceCap
    positivity
  have hf : 0 ≤ nativeSourceFullResponseCap M.gamma height := by
    unfold nativeSourceFullResponseCap Inverse.rawTraceFullResponseCap
    positivity
  have hprofiles := heat_source_profiles_le_old M.gamma height hg0 hg (by dsimp [height]; omega)
  have hdom := native_source_generic_individual_degree_split height
    (theta:=1) (a:=((3/50:ℝ)*theta M)) (a0:=(nativeA:ℝ))
    (e:=nativeSourceRawShellVarianceCap M.gamma height) (e0:=(old.e:ℝ))
    (f:=nativeSourceFullResponseCap M.gamma height) (f0:=(old.f:ℝ))
    (by norm_num) (by norm_num) (by positivity) (by norm_num [nativeA])
    (by simpa only [one_mul,nativeA,Rat.cast_div,Rat.cast_ofNat] using
      mul_le_of_le_one_right (by norm_num : (0:ℝ)≤3/50) ht1)
    he (by exact_mod_cast hv.1) (by simpa only [one_mul] using hprofiles.1)
    hf (by exact_mod_cast hv.2.2.1) hprofiles.2 4
  simp only [one_mul] at hdom
  have hfull := hdom.trans (heat_configured_old_real_profile index)
  have hcap := native_source_band_four_pass_W (W := W) M h hM hg n hpast hstate height hgap.1
  intro t ht
  exact (hcap t ht).trans (ENNReal.ofReal_le_ofReal hfull)

end
end ASDExplicitGamma.Native
