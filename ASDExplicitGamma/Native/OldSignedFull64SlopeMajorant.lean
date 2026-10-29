module

public import ASDExplicitGamma.Native.OldSignedFull64ClockAlgebra

/-! A theta-scaled summable majorant of the actual full64 OLD depth control. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Cold Algsuperdiff.Section3
noncomputable section

/-- Fixed rational affine-geometric auxiliary history slope. -/
def oldSignedFull64SlopeMajorant (j : ℕ) : ℝ :=
  (383/250000)*(120*(251/250)*(17/20:ℝ)^j+
    (28/125)*(509/500)*(2050+6*(j:ℝ))*(1/10:ℝ)^j)

/-- The actual pre-insertion state supplies the theta-scaled physical
variance cap; the molecular viscosity is never used as the response frame. -/
theorem old_signed_full64_variance_cap (M : ABKModel 2) (h : ℝ) (n : ℤ)
    (hg : M.gamma≤gammaZero) (hstate : nativeInductionState M h n) :
    (q3ModelAmplitude M h (n+1))^2/(Annealed.sigmaBar M n:ℝ)^2 ≤
      theta M*(383/250000) := by
  have hv := source_native_shell_variance_clock M h n (n+1) hstate
  norm_num only [Int.cast_add,Int.cast_one,add_sub_cancel_left,mul_one] at hv
  have he := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3)
    (mul_le_mul_of_nonneg_left hg (by norm_num : (0:ℝ)≤2))
  have hh := mul_le_mul_of_nonneg_left (he.trans old_signed_full64_clock_caps.1)
    (mul_nonneg (by norm_num : (0:ℝ)≤9/2) M.shellPrefix.gamma_pos.le)
  apply hv.trans (hh.trans ?_)
  unfold theta gammaZero
  nlinarith only [M.shellPrefix.gamma_pos.le]

/-- The physical depth control has the retained rational summable majorant.
All clocks and the variance are derived from the actual model and past state. -/
theorem old_signed_full64_depth_majorant (M : ABKModel 2) (h : ℝ) (n : ℤ)
    (hg : M.gamma≤gammaZero) (hstate : nativeInductionState M h n) (j : ℕ) :
    coldHistoryBeta^j*oldSignedP20Full64Control M h n j ≤ theta M*oldSignedFull64SlopeMajorant j := by
  let C := rawTraceOldFrameP20LocalClock M.gamma (6+j)
  let F := oldSignedP20Full64Cap M.gamma (6+j)
  let z := (1/3:ℝ)^j
  have hβ : 0≤coldHistoryBeta^j := pow_nonneg coldHistoryBeta_pos.le j
  have hθ : 0≤theta M := (cold_theta_pos M).le
  have hC0 : 0≤C := by dsimp [C,rawTraceOldFrameP20LocalClock]; positivity
  have hF0 : 0≤F := by dsimp [F,oldSignedP20Full64Cap]; have hg0 := M.shellPrefix.gamma_pos.le; positivity
  have hlin := old_signed_full64_linear_clock_le M.gamma hg j
  have hprod := old_signed_full64_response_clock_le M.gamma M.shellPrefix.gamma_pos.le hg j
  have hfirst : coldHistoryBeta^j*(120*C)≤120*(251/250)*(17/20:ℝ)^j := by
    have hh := mul_le_mul_of_nonneg_left hlin (mul_nonneg hβ (by norm_num : (0:ℝ)≤120))
    have hp := pow_le_pow_left₀ (mul_nonneg coldHistoryBeta_pos.le (by positivity))
      old_signed_full64_slope_ratios.1 j
    have hp' := mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ)≤120*(251/250))
    rw [mul_pow] at hp'
    dsimp [C] at *
    nlinarith only [hh,hp']
  have hsecond : coldHistoryBeta^j*((7/125)*z^2*C^2*F)≤
      (28/125)*(509/500)*(2050+6*(j:ℝ))*(1/10:ℝ)^j := by
    have hz2 : z^2=(1/9:ℝ)^j := by
      dsimp [z]
      rw [←pow_mul,Nat.mul_comm j 2,pow_mul]
      norm_num
    have heq : coldHistoryBeta^j*z^2*((3:ℝ)^(8*gammaZero))^j=
        (coldHistoryBeta*(3:ℝ)^(8*gammaZero)/9)^j := by
      rw [hz2,←mul_pow,←mul_pow]
      congr 1
      ring
    have hh := mul_le_mul_of_nonneg_left hprod
      (mul_nonneg (mul_nonneg hβ (by norm_num : (0:ℝ)≤7/125)) (sq_nonneg z))
    have hp := pow_le_pow_left₀ (div_nonneg (mul_nonneg coldHistoryBeta_pos.le (by positivity)) (by norm_num))
      old_signed_full64_slope_ratios.2 j
    have hp' := mul_le_mul_of_nonneg_left hp
      (by positivity : (0:ℝ)≤(28/125)*(509/500)*(2050+6*(j:ℝ)))
    calc
      _ ≤ (28/125)*(509/500)*(2050+6*(j:ℝ))*
          (coldHistoryBeta^j*z^2*((3:ℝ)^(8*gammaZero))^j) := by
        convert hh using 1 <;> ring
      _ ≤ _ := by rw [heq]; exact hp'
  have hb := add_le_add hfirst hsecond
  have hv := old_signed_full64_variance_cap M h n hg hstate
  have hcontrol := old_signed_full64_control_decay M h n j
  have hbrace : 0≤120*C+(7/125)*z^2*C^2*F := by positivity
  have hscaled := mul_le_mul_of_nonneg_left
    (hcontrol.trans (mul_le_mul_of_nonneg_right hv hbrace)) hβ
  have hfinal := mul_le_mul_of_nonneg_left hb
    (mul_nonneg hθ (by norm_num : (0:ℝ)≤383/250000))
  dsimp [oldSignedFull64SlopeMajorant]
  calc
    _ ≤ coldHistoryBeta^j*(theta M*(383/250000)*(120*C+(7/125)*z^2*C^2*F)) := hscaled
    _ ≤ _ := by convert hfinal using 1 <;> ring

end
end ASDExplicitGamma.Native
