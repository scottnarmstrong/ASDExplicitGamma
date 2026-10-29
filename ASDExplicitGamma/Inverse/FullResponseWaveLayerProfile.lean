module

public import ASDExplicitGamma.Inverse.WeightedLocalizationLayerProfile
public import ASDExplicitGamma.Inverse.RootDefinitions

/-! Exact retained volume profiles for the full-response wave payment. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
noncomputable section

/-- A(4γ), with the exact physical planar layer weights. -/
def fullResponseWaveLayerMass (γ : ℝ) : ℝ :=
  8*localizationProfileT (1/3) ((3:ℝ)^(4*γ)) -
    32*localizationProfileT (1/9) ((3:ℝ)^(4*γ)) + ((3:ℝ)^(4*γ))^2

/-- A_f(4γ), retaining the first profile-depth moment. -/
def fullResponseWaveLayerFirst (γ : ℝ) : ℝ :=
  8*localizationProfileTf (1/3) ((3:ℝ)^(4*γ)) -
    32*localizationProfileTf (1/9) ((3:ℝ)^(4*γ)) + 2*((3:ℝ)^(4*γ))^2

/-- Both exact source profiles are sums of the actual positive layer weights. -/
theorem full_response_wave_layer_profiles (γ : ℝ) (hg : γ ≤ gammaZero) :
    HasSum (fun k : ℕ => bankLayerWeight k*
      (3:ℝ)^(4*γ*(localizationProfileDepth (k+1):ℝ)))
      (fullResponseWaveLayerMass γ) ∧
    HasSum (fun k : ℕ => (localizationProfileDepth (k+1):ℝ)*bankLayerWeight k*
      (3:ℝ)^(4*γ*(localizationProfileDepth (k+1):ℝ)))
      (fullResponseWaveLayerFirst γ) := by
  let z := (3:ℝ)^(4*γ)
  have hz : 0 ≤ z := by dsimp only [z]; positivity
  have hsmall : z^4 < 27 := by
    calc
      z^4 = (3:ℝ)^((4*γ)*(4:ℕ)) := (Real.rpow_mul_natCast (by norm_num) _ _).symm
      _ < (3:ℝ)^(3:ℝ) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
        (by change γ ≤ 17/50000 at hg; norm_num; linarith only [hg])
      _ = 27 := by norm_num
  have he (k : ℕ) : z^localizationProfileDepth (k+1) =
      (3:ℝ)^(4*γ*(localizationProfileDepth (k+1):ℝ)) :=
    (Real.rpow_mul_natCast (by norm_num) _ _).symm
  constructor
  · simpa only [he, fullResponseWaveLayerMass, z] using localization_layer_profile_hasSum z hz hsmall
  · simpa only [he, fullResponseWaveLayerFirst, z] using localization_layer_profile_moment_hasSum z hz hsmall

/-- The complete deterministic identity-wave norm payments retain exactly
W₀*(D*A+A_f)+W₁*A before any numerical upper bound is substituted. -/
theorem full_response_identity_wave_budget_hasSum
    (γ D W0 W1 : ℝ) (hg : γ ≤ gammaZero) :
    HasSum (fun k : ℕ => (γ*(3:ℝ)^(2*γ*D)/4)*bankLayerWeight k*
      (3:ℝ)^(4*γ*(localizationProfileDepth (k+1):ℝ))*
        ((D+(localizationProfileDepth (k+1):ℝ))*W0+W1))
      ((γ*(3:ℝ)^(2*γ*D)/4)*
        (W0*(D*fullResponseWaveLayerMass γ+fullResponseWaveLayerFirst γ)+
          W1*fullResponseWaveLayerMass γ)) := by
  obtain ⟨h0,h1⟩ := full_response_wave_layer_profiles γ hg
  have hh := (((h0.mul_left D).add h1).mul_left W0).add (h0.mul_left W1)
  convert hh.mul_left (γ*(3:ℝ)^(2*γ*D)/4) using 1
  funext k
  ring

end
end ASDExplicitGamma.Inverse
