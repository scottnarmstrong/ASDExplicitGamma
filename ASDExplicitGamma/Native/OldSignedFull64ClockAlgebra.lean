module

public import ASDExplicitGamma.Native.OldSignedFull64Endpoint

/-! Exact affine-geometric clocks for the auxiliary full64 history slope. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Inverse Cold
noncomputable section

/-- The inverse clock separates into its fixed five-level loss and depth. -/
theorem old_signed_full64_linear_clock_eq (gamma : ℝ) (j : ℕ) :
    rawTraceOldFrameP20LocalClock gamma (6+j)=
      (3:ℝ)^(10*gamma)*((3:ℝ)^(2*gamma))^j := by
  unfold rawTraceOldFrameP20LocalClock
  rw [←Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤3),←Real.rpow_add (by norm_num : (0:ℝ)<3)]
  congr 1
  push_cast
  ring

/-- The squared inverse clock times the full response is exactly an
 affine times a geometric depth factor, before taking endpoint bounds. -/
theorem old_signed_full64_response_clock_eq (gamma : ℝ) (j : ℕ) :
    rawTraceOldFrameP20LocalClock gamma (6+j)^2*oldSignedP20Full64Cap gamma (6+j)=
      4*((2018618/1000000:ℝ)+gamma*(16684*7+5899542)+16684*gamma*(j:ℝ))*
        (3:ℝ)^(46*gamma)*((3:ℝ)^(8*gamma))^j := by
  have hp : ((3:ℝ)^(2*gamma*(((6+j:ℕ):ℝ)-1)))^2*
      (3:ℝ)^(2*gamma*((6+j+1:ℕ):ℝ)+2*gamma*((6+j:ℕ):ℝ))=
      (3:ℝ)^(46*gamma)*((3:ℝ)^(8*gamma))^j := by
    rw [←Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤3),
      ←Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤3),
      ←Real.rpow_add (by norm_num : (0:ℝ)<3),←Real.rpow_add (by norm_num : (0:ℝ)<3)]
    congr 1
    push_cast
    ring
  have ha : (2018618/1000000:ℝ)+gamma*(16684*((6+j+1:ℕ):ℝ)+5899542)=
      (2018618/1000000:ℝ)+gamma*(16684*7+5899542)+16684*gamma*(j:ℝ) := by
    push_cast
    ring
  unfold rawTraceOldFrameP20LocalClock oldSignedP20Full64Cap
  rw [ha]
  calc
    _ = (4*((2018618/1000000:ℝ)+gamma*(16684*7+5899542)+16684*gamma*(j:ℝ)))*
      (((3:ℝ)^(2*gamma*(((6+j:ℕ):ℝ)-1)))^2*
      (3:ℝ)^(2*gamma*((6+j+1:ℕ):ℝ)+2*gamma*((6+j:ℕ):ℝ))) := by ring
    _ = _ := by rw [hp]; ring

/-- Endpoint comparison of the linear clock. -/
theorem old_signed_full64_linear_clock_le (gamma : ℝ) (hg : gamma≤gammaZero) (j : ℕ) :
    rawTraceOldFrameP20LocalClock gamma (6+j)≤
      (251/250:ℝ)*((3:ℝ)^(2*gammaZero))^j := by
  rw [old_signed_full64_linear_clock_eq]
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3)
    (mul_le_mul_of_nonneg_left hg (by norm_num : (0:ℝ)≤10))
  have hq := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3)
    (mul_le_mul_of_nonneg_left hg (by norm_num : (0:ℝ)≤2))
  exact mul_le_mul (hp.trans old_signed_full64_clock_caps.2.2.1)
    (pow_le_pow_left₀ (by positivity) hq j) (by positivity) (by norm_num)

/-- Endpoint comparison of the full affine response clock; the j term is
retained for its Eulerian sum. -/
theorem old_signed_full64_response_clock_le (gamma : ℝ) (_hg0 : 0≤gamma)
    (hg : gamma≤gammaZero) (j : ℕ) :
    rawTraceOldFrameP20LocalClock gamma (6+j)^2*oldSignedP20Full64Cap gamma (6+j)≤
      4*(2050+6*(j:ℝ))*(509/500)*((3:ℝ)^(8*gammaZero))^j := by
  rw [old_signed_full64_response_clock_eq]
  have ha : (2018618/1000000:ℝ)+gamma*(16684*7+5899542)≤2050 := by
    norm_num [gammaZero] at hg
    linarith only [hg]
  have hs : 16684*gamma≤6 := by
    norm_num [gammaZero] at hg
    linarith only [hg]
  have hlin := add_le_add ha (mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg j))
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3)
    (mul_le_mul_of_nonneg_left hg (by norm_num : (0:ℝ)≤46))
  have hq := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3)
    (mul_le_mul_of_nonneg_left hg (by norm_num : (0:ℝ)≤8))
  exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hlin (by norm_num))
    (hp.trans old_signed_full64_clock_caps.2.2.2) (by positivity) (by positivity))
    (pow_le_pow_left₀ (by positivity) hq j) (by positivity) (by positivity)

end
end ASDExplicitGamma.Native
