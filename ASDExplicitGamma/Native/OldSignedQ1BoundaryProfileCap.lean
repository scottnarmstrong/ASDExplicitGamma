module

public import ASDExplicitGamma.Native.OldSignedQ1MultiplierCaps

/-! Actual covariance-boundary profile fits the exact frozen q1 coefficient. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Gaussian Main Triadic Cold Algsuperdiff.Section3 Numerics.Native
noncomputable section

/-- Every physical setup field is nonnegative by its exact interval certificate. -/
theorem old_signed_q1_setup_field_nonneg (i : Fin 17) :
    0≤nativeSetupQ1001FieldsR.getD i.val 0 :=
  (Rat.cast_nonneg.mpr (nativeSetupQ1001Fields_lower i)).trans (nativeSetupQ1001Fields_sound i.val).1

/-- The actual complete covariance boundary coefficient has degree theta,
with exactly the endpoint coefficient used by both frozen boundary terms. -/
theorem old_signed_q1_scaled_boundary_profile
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma≤gammaZero) (n : ℤ)
    (hstate : nativeInductionState M h n) :
    let b := q3ModelAmplitude M h (n+1)/(Annealed.sigmaBar M n:ℝ)
    let L := q3ModelLength (n+1)
    b^2+3*(cubeScaleFactor (originCube 2 n)/3^5)*planarC1*|b| *Real.sqrt (mainFlatSigmaSq b L)≤
      theta M*(nativeSetupQ1001FieldsR.getD 6 0) := by
  intro b L
  let r := cubeScaleFactor (originCube 2 n)/3^5
  let v := nativeSetupQ1001FieldsR.getD 0 0
  let S := v*(1/531441)*(156/5)
  have hr : 0≤r := div_nonneg (Triadic.cubeScaleFactor_pos' _).le (by positivity)
  have h0 := old_signed_q1_model_variance M h hg n hstate
  have ha := old_signed_q1_scaled_amplitude M h hg n hstate
  have hG := old_signed_q1_scaled_gradient_root M h hg n hstate
  have hprod := mul_le_mul ha hG (mul_nonneg hr (Real.sqrt_nonneg _))
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hp : |b| *(r*Real.sqrt (mainFlatSigmaSq b L))≤theta M*(Real.sqrt v*Real.sqrt S) := by
    calc
      _ ≤ (Real.sqrt (theta M)*Real.sqrt v)*(Real.sqrt (theta M)*Real.sqrt S) := hprod
      _ = (Real.sqrt (theta M))^2*(Real.sqrt v*Real.sqrt S) := by ring
      _ = _ := by rw [Real.sq_sqrt (cold_theta_pos M).le]
  have hc : planarC1≤(38/125:ℝ) := native_boundary_planarC1_le.trans_eq (by norm_num)
  have hb := mul_le_mul hc hp (mul_nonneg (abs_nonneg b) (mul_nonneg hr (Real.sqrt_nonneg _)))
    (by norm_num : (0:ℝ)≤38/125)
  have hh := add_le_add h0 (mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ)≤3))
  rw [old_signed_q1_setup_readable_06]
  convert hh using 1 <;> dsimp only [r,v,S] <;> ring

end
end ASDExplicitGamma.Native
