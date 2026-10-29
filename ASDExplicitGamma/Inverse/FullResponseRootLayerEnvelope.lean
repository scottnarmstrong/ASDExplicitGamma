module

public import ASDExplicitGamma.Inverse.WeightedLocalizationProfileNumerics
public import ASDExplicitGamma.Inverse.FullResponseWaveLayerProfile

/-! The corrected positive square-root layer envelope used only in combination. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open ASDExplicitGamma.Numerics.Inverse
noncomputable section

/-- The central layer is kept exact; later layers use the literal source
positive envelope of the source. -/
def fullResponseRootLayerEnvelope (k : ℕ) : ℝ :=
  if k=0 then 1/3 else (2829/1000:ℝ)*(invLayerRoot:ℝ)^(k+1)

/-- The corrected positive envelope bounds the actual square-root volume. -/
theorem full_response_root_layer_sqrt_le (k : ℕ) :
    Real.sqrt (bankLayerWeight k) ≤ fullResponseRootLayerEnvelope k := by
  have hr0 : (0:ℝ) < (invLayerRoot:ℝ) := by exact_mod_cast invLayerRoot_bracket.1
  have hr : (1/3:ℝ) ≤ (invLayerRoot:ℝ)^2 := by
    have hh := Rat.cast_lt (K := ℝ).mpr invLayerRoot_bracket.2
    norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,Rat.cast_pow] at hh
    exact hh.le
  cases k with
  | zero =>
    simp only [fullResponseRootLayerEnvelope,ite_true,layerWeight_zero]
    apply (Real.sqrt_le_left (by norm_num)).mpr
    norm_num
  | succ k =>
    rw [fullResponseRootLayerEnvelope,ite_eq_right (by omega)]
    apply (Real.sqrt_le_left (by positivity)).mpr
    have hv : bankLayerWeight (k+1) ≤ 8*(1/3:ℝ)^(k+2) := by
      rw [layerWeight_succ]
      have hh : 0 ≤ 32*(1/9:ℝ)^(k+2) := by positivity
      linarith only [hh]
    have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/3) hr (k+2)
    have hc : (8:ℝ) ≤ (2829/1000:ℝ)^2 := by norm_num
    have hz : (0:ℝ) ≤ ((invLayerRoot:ℝ)^2)^(k+2) := by positivity
    apply hv.trans
    calc
      _ ≤ 8*((invLayerRoot:ℝ)^2)^(k+2) := mul_le_mul_of_nonneg_left hp (by norm_num)
      _ ≤ (2829/1000:ℝ)^2*((invLayerRoot:ℝ)^2)^(k+2) := mul_le_mul_of_nonneg_right hc hz
      _ = _ := by rw [mul_pow,← pow_mul,← pow_mul]; congr 2; omega

/-- The source positive L0 profile of the actual corrected envelope. -/
def fullResponseRootLayerMass (z : ℝ) : ℝ :=
  z^2/3+(2829/1000:ℝ)*(localizationProfileT (invLayerRoot:ℝ) z-(invLayerRoot:ℝ)*z^2)

/-- Its first depth moment; only the combined L1/L0 comparison is used later. -/
def fullResponseRootLayerFirst (z : ℝ) : ℝ :=
  2*z^2/3+(2829/1000:ℝ)*(localizationProfileTf (invLayerRoot:ℝ) z-2*(invLayerRoot:ℝ)*z^2)

/-- Exact sums of the corrected positive square-root envelopes. -/
theorem full_response_root_layer_profiles (z : ℝ) (hz : 0 ≤ z)
    (hsmall : (invLayerRoot:ℝ)^3*z^4 < 1) :
    HasSum (fun k : ℕ => fullResponseRootLayerEnvelope k*z^localizationProfileDepth (k+1))
      (fullResponseRootLayerMass z) ∧
    HasSum (fun k : ℕ => (localizationProfileDepth (k+1):ℝ)*
      fullResponseRootLayerEnvelope k*z^localizationProfileDepth (k+1))
      (fullResponseRootLayerFirst z) := by
  have hr : (0:ℝ) ≤ (invLayerRoot:ℝ) := by exact_mod_cast invLayerRoot_bracket.1.le
  have h0 := (localization_profile_hasSum (invLayerRoot:ℝ) z hr hz hsmall).mul_left (2829/1000:ℝ)
  have h1 := (localization_profile_moment_hasSum (invLayerRoot:ℝ) z hr hz hsmall).mul_left (2829/1000:ℝ)
  have hs0 : HasSum (fun k : ℕ => if k=0 then
      ((1/3:ℝ)-(2829/1000)*(invLayerRoot:ℝ))*z^2 else 0)
      (((1/3:ℝ)-(2829/1000)*(invLayerRoot:ℝ))*z^2) := hasSum_ite_eq 0 _
  have hs1 := hs0.mul_left 2
  constructor
  · convert h0.add hs0 using 1
    · funext k
      cases k with
      | zero => norm_num [fullResponseRootLayerEnvelope,localizationProfileDepth]; ring
      | succ k => simp only [fullResponseRootLayerEnvelope,Nat.succ_ne_zero,ite_false]; ring
    · dsimp only [fullResponseRootLayerMass]
      ring
  · convert h1.add hs1 using 1
    · funext k
      cases k with
      | zero => norm_num [fullResponseRootLayerEnvelope,localizationProfileDepth]; ring
      | succ k => simp only [fullResponseRootLayerEnvelope,Nat.succ_ne_zero,ite_false,mul_zero,add_zero]; ring
    · dsimp only [fullResponseRootLayerFirst]
      ring

end
end ASDExplicitGamma.Inverse
