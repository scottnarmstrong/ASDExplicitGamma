module

public import ASDExplicitGamma.Native.GenericSourceChildAuxNumerics
public import ASDExplicitGamma.Native.GenericSourceChildBandResponse

/-! Physical variance and full128 inputs for the two auxiliary child barriers. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Algsuperdiff.Section3 ASDExplicitGamma.Inverse
noncomputable section

/-- The entire physical child-band variance has the required proportional
auxiliary cap throughout either finite comparison range. -/
theorem native_source_child_aux_variance
    (M : ABKModel 2) (hg : M.gamma ≤ gammaZero) (height : ℕ) (high : Bool)
    (hh : height ≤ nativeSourceChildAuxHeight high) :
    nativeSourceRawShellVarianceCap M.gamma height ≤
      theta M*(nativeSourceChildAuxVariance high:ℝ) := by
  have hg0 := M.shellPrefix.gamma_pos.le
  have ht0 : 0 ≤ theta M := div_nonneg hg0 (by norm_num [gammaZero])
  let H := nativeSourceChildAuxHeight high
  have hH : H ≤ 160 := by cases high <;> norm_num [H,nativeSourceChildAuxHeight]
  have hhR : (height:ℝ) ≤ (H:ℝ) := by exact_mod_cast hh
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3)
    (mul_le_mul_of_nonneg_right (show 2*(height:ℝ) ≤ 2*(H:ℝ) by linarith only [hhR]) hg0)
  have hmono : nativeSourceRawShellVarianceCap M.gamma height ≤ nativeSourceRawShellVarianceCap M.gamma H :=
    mul_le_mul_of_nonneg_left hp (mul_nonneg (by norm_num : (0:ℝ)≤9/2) hg0)
  have htrue := native_source_true_variance_le_generic M.gamma H hg0 hg (by omega)
  have hdeg := native_source_generic_variance_cap_degree M.gamma (theta M) H hg0 hg rfl (by omega)
  have hnum : nativeSourceGenericVarianceCap (17/50000) H ≤ (nativeSourceChildAuxVariance high:ℝ) := by
    cases high <;> norm_num [H,nativeSourceChildAuxHeight,nativeSourceChildAuxVariance,
      nativeSourceGenericVarianceCap,nativeSourceE]
  exact hmono.trans (htrue.trans (hdeg.trans (mul_le_mul_of_nonneg_left hnum ht0)))

/-- The child full128 trace cap stays below the auxiliary rational payment
on the chosen finite comparison range. -/
theorem native_source_child_aux_response
    (M : ABKModel 2) (hg : M.gamma ≤ gammaZero) (height : ℕ) (high : Bool)
    (hh : height ≤ nativeSourceChildAuxHeight high) :
    nativeSourceChildFullResponseCap M.gamma height ≤ (nativeSourceChildAuxResponse high:ℝ) := by
  have hg0 := M.shellPrefix.gamma_pos.le
  let H := nativeSourceChildAuxHeight high
  let γ0 : ℝ := 17/50000
  let t := (2*(H:ℝ)+8)*γ0
  have hhR : (height:ℝ) ≤ (H:ℝ) := by exact_mod_cast hh
  have ht : 0 ≤ t := by dsimp [t,γ0]; positivity
  have hdomain : (11/10:ℝ)*t<1 := by
    cases high <;> norm_num [t,γ0,H,nativeSourceChildAuxHeight]
  have hp0 := Numerics.Inverse.inv_three_power_bound t ht hdomain
  have hp : (3:ℝ)^t ≤ (1-(11/10:ℝ)*t)⁻¹ := by simpa only [one_div] using hp0
  have hexp : (2*(height:ℝ)+8)*M.gamma ≤ t := by
    calc
      _ ≤ (2*(H:ℝ)+8)*M.gamma := mul_le_mul_of_nonneg_right (by linarith only [hhR]) hg0
      _ ≤ _ := mul_le_mul_of_nonneg_left hg (by positivity)
  have hpow := (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3) hexp).trans hp
  have hpoly : (1009309/500000:ℝ)+M.gamma*(32474*((height:ℝ)+2)+11483216) ≤
      (1009309/500000:ℝ)+γ0*(32474*((H:ℝ)+2)+11483216) := by
    apply add_le_add le_rfl
    apply mul_le_mul hg
    · linarith only [hhR]
    · positivity
    · norm_num [γ0,gammaZero]
  have hright : 0 ≤ (1009309/500000:ℝ)+γ0*(32474*((H:ℝ)+2)+11483216) := by
    dsimp [γ0]
    positivity
  have hc := mul_le_mul (mul_le_mul_of_nonneg_left hpoly (by norm_num : (0:ℝ)≤4)) hpow
    (Real.rpow_nonneg (by norm_num : (0:ℝ)≤3) _) (mul_nonneg (by norm_num) hright)
  change nativeSourceChildFullResponseCap M.gamma height ≤
    4*((1009309/500000:ℝ)+γ0*(32474*((H:ℝ)+2)+11483216))*(1-(11/10:ℝ)*t)⁻¹ at hc
  apply hc.trans
  cases high <;> norm_num [γ0,H,t,nativeSourceChildAuxHeight,nativeSourceChildAuxResponse]

end
end ASDExplicitGamma.Native
