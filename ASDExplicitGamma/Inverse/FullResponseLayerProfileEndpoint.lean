module

public import ASDExplicitGamma.Inverse.FullResponseSelectedEndpoint
public import ASDExplicitGamma.Inverse.BankRootProfileArithmetic

/-! The exact retained physical layer profiles consume their rational caps. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open ASDExplicitGamma.Numerics.Inverse
noncomputable section

/-- The identity retained A(4gamma) and A_f(4gamma) fit the exact outward
source suppliers, with monotonicity proved from positive physical weights. -/
theorem full_response_wave_layer_endpoint (γ : ℝ) (hg : γ ≤ gammaZero) :
    fullResponseWaveLayerMass γ ≤ (invLayer (4*invGamma):ℝ) ∧
      fullResponseWaveLayerFirst γ ≤ (invLayerF (4*invGamma):ℝ) := by
  let z := (3:ℝ)^(4*γ)
  let z0 := (invLayerZ:ℝ)
  have hz : 0 ≤ z := by dsimp only [z]; positivity
  have hzz : z ≤ z0 := full_response_layer_clock_le γ hg
  have hzsmall : z0^4 < 27 := by norm_num [z0,invLayerZ,invE,invGamma]
  have hmass := localization_layer_profile_mono hz hzz hzsmall
  have hfirst := localization_layer_profile_moment_mono hz hzz hzsmall
  have hm : 8*localizationProfileT (1/3) z0-32*localizationProfileT (1/9) z0+z0^2 =
      (invExactLayerFour:ℝ) := by
    dsimp only [z0]
    rw [show (1/3:ℝ)=((1/3:ℚ):ℝ) by norm_num,show (1/9:ℝ)=((1/9:ℚ):ℝ) by norm_num,
      localization_profileT_numeric (1/3) invLayerZ,localization_profileT_numeric (1/9) invLayerZ]
    norm_num [invExactLayerFour,invLayerZ,invT,invE,invGamma]
  have hf : 8*localizationProfileTf (1/3) z0-32*localizationProfileTf (1/9) z0+2*z0^2 =
      ((8*invTf (1/3) (invE (11/10*4*invGamma))-
        32*invTf (1/9) (invE (11/10*4*invGamma))+2*(invE (11/10*4*invGamma))^2:ℚ):ℝ) := by
    dsimp only [z0]
    rw [show (1/3:ℝ)=((1/3:ℚ):ℝ) by norm_num,show (1/9:ℝ)=((1/9:ℚ):ℝ) by norm_num,
      localization_profileTf_numeric (1/3) invLayerZ,localization_profileTf_numeric (1/9) invLayerZ]
    norm_num [invLayerZ,invTf,invE,invGamma]
  have hmn : (invExactLayerFour:ℝ) ≤ (invLayer (4*invGamma):ℝ) := by exact_mod_cast invLayer_majorant_Four.le
  have hfn := (Rat.cast_lt (K := ℝ)).mpr invLayerF_majorant
  constructor
  · exact (hmass.trans_eq hm).trans hmn
  · exact (hfirst.trans_eq hf).trans hfn.le

end
end ASDExplicitGamma.Inverse
