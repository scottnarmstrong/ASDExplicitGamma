module

public import ASDExplicitGamma.Inverse.FullResponseRootLayerEnvelope
public import ASDExplicitGamma.Numerics.Inverse.RealBounds

/-! Endpoint clock and the corrected positive layer envelopes. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open ASDExplicitGamma.Numerics.Inverse
noncomputable section

/-- The retained physical four-gamma clock is below the rational layer endpoint. -/
theorem full_response_layer_clock_le (γ : ℝ) (hg : γ ≤ gammaZero) :
    (3:ℝ)^(4*γ) ≤ (invLayerZ:ℝ) := by
  have hg' : γ ≤ (invGamma:ℝ) := by simpa only [gammaZero,invGamma,Rat.cast_div,
    Rat.cast_ofNat] using hg
  have hh := inv_three_power_bound (4*(invGamma:ℝ)) (by norm_num [invGamma])
    (by norm_num [invGamma])
  apply (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3)
    (mul_le_mul_of_nonneg_left hg' (by norm_num : (0:ℝ) ≤ 4))).trans
  convert hh using 1
  norm_num [invLayerZ,invE,invGamma]

/-- Both exact positive envelope series converge at the literal rational endpoint. -/
theorem full_response_root_layer_endpoint_profiles :
    HasSum (fun k : ℕ => fullResponseRootLayerEnvelope k*
      (invLayerZ:ℝ)^localizationProfileDepth (k+1)) (invL0plus:ℝ) ∧
    HasSum (fun k : ℕ => (localizationProfileDepth (k+1):ℝ)*
      fullResponseRootLayerEnvelope k*(invLayerZ:ℝ)^localizationProfileDepth (k+1))
      (invL1plus:ℝ) := by
  have hz : (0:ℝ) ≤ (invLayerZ:ℝ) := by norm_num [invLayerZ,invE,invGamma]
  have hs : (invLayerRoot:ℝ)^3*(invLayerZ:ℝ)^4 < 1 := by
    have hh := invLayer_domains.2.1
    exact_mod_cast (sub_pos.mp hh)
  have hh := full_response_root_layer_profiles (invLayerZ:ℝ) hz hs
  have h0 : fullResponseRootLayerMass (invLayerZ:ℝ) = (invL0plus:ℝ) := by
    unfold fullResponseRootLayerMass
    rw [localization_profileT_numeric invLayerRoot invLayerZ]
    unfold invL0plus
    push_cast
    ring
  have h1 : fullResponseRootLayerFirst (invLayerZ:ℝ) = (invL1plus:ℝ) := by
    unfold fullResponseRootLayerFirst
    rw [localization_profileTf_numeric invLayerRoot invLayerZ]
    unfold invL1plus
    push_cast
    ring
  exact ⟨h0 ▸ hh.1,h1 ▸ hh.2⟩

/-- Corrected square-root volume and retained clock jointly fit the source
positive endpoint, keeping the central layer exact. -/
theorem full_response_root_layer_clock_le (γ : ℝ) (hg : γ ≤ gammaZero) (k : ℕ) :
    Real.sqrt (bankLayerWeight k)*(3:ℝ)^(4*γ*(localizationProfileDepth (k+1):ℝ)) ≤
      fullResponseRootLayerEnvelope k*(invLayerZ:ℝ)^localizationProfileDepth (k+1) := by
  have he : (3:ℝ)^(4*γ*(localizationProfileDepth (k+1):ℝ)) =
      ((3:ℝ)^(4*γ))^localizationProfileDepth (k+1) :=
    Real.rpow_mul_natCast (by norm_num) _ _
  rw [he]
  exact mul_le_mul (full_response_root_layer_sqrt_le k)
    (pow_le_pow_left₀ (by positivity) (full_response_layer_clock_le γ hg) _)
    (by positivity) ((Real.sqrt_nonneg _).trans (full_response_root_layer_sqrt_le k))

end
end ASDExplicitGamma.Inverse
