module

public import ASDExplicitGamma.Native.OldSignedMeanSourceDecay
public import ASDExplicitGamma.Native.OldSignedFull64SlopeMajorant

/-! Fixed rational geometric majorants for the actual OLD source mean slopes. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Gaussian Scalar Inverse Cold Algsuperdiff.Section3
noncomputable section

/-- Retained slow inverse clock and fast covariance decay of the mean slope. -/
def oldSignedMeanSlopeMajorant (j : ℕ) : ℝ :=
  (383/250000)*(3*(251/250)*(1001/1000:ℝ)^j+
    (3/625)*(509/500)*(2050+6*(j:ℝ))*(14/125:ℝ)^j)

/-- Actual first-moment source slopes obey the fixed rational profile. -/
theorem old_signed_mean_source_majorant (M : ABKModel 2) (h : ℝ) (n : ℤ)
    (hg : M.gamma≤gammaZero) (hstate : nativeInductionState M h n) (j : ℕ) :
    oldSignedMeanSourceCap M h n (5+j) ≤ theta M*oldSignedMeanSlopeMajorant j := by
  let C := rawTraceOldFrameP20LocalClock M.gamma (6+j)
  let F := oldSignedP20Full64Cap M.gamma (6+j)
  let z := (1/3:ℝ)^j
  have hθ : 0≤theta M := (cold_theta_pos M).le
  have hC0 : 0≤C := by dsimp [C,rawTraceOldFrameP20LocalClock]; positivity
  have hF0 : 0≤F := by dsimp [F,oldSignedP20Full64Cap]; have hg0 := M.shellPrefix.gamma_pos.le; positivity
  have hlin := old_signed_full64_linear_clock_le M.gamma hg j
  have hprod := old_signed_full64_response_clock_le M.gamma M.shellPrefix.gamma_pos.le hg j
  have hfirst : 3*C≤3*(251/250)*(1001/1000:ℝ)^j := by
    have hp := pow_le_pow_left₀ (by positivity : (0:ℝ)≤(3:ℝ)^(2*gammaZero))
      old_signed_full64_clock_caps.1 j
    have hh := hlin.trans (mul_le_mul_of_nonneg_left hp (by norm_num))
    have hh' := mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ)≤3)
    simpa only [mul_assoc] using hh'
  have hsecond : (3/2500)*z^2*C^2*F≤
      (3/625)*(509/500)*(2050+6*(j:ℝ))*(14/125:ℝ)^j := by
    have hz2 : z^2=(1/9:ℝ)^j := by
      dsimp [z]
      rw [←pow_mul,Nat.mul_comm j 2,pow_mul]
      norm_num
    have heq : z^2*((3:ℝ)^(8*gammaZero))^j=((3:ℝ)^(8*gammaZero)/9)^j := by
      rw [hz2,←mul_pow]
      congr 1
      ring
    have hratio : (3:ℝ)^(8*gammaZero)/9≤14/125 := by
      exact (div_le_div_of_nonneg_right old_signed_full64_clock_caps.2.1
        (by norm_num : (0:ℝ)≤9)).trans (by norm_num)
    have hh := mul_le_mul_of_nonneg_left hprod
      (by positivity : (0:ℝ)≤(3/2500)*z^2)
    have hp := pow_le_pow_left₀ (by positivity : (0:ℝ)≤(3:ℝ)^(8*gammaZero)/9) hratio j
    have hp' := mul_le_mul_of_nonneg_left hp
      (by positivity : (0:ℝ)≤(3/625)*(509/500)*(2050+6*(j:ℝ)))
    calc
      _ ≤ (3/625)*(509/500)*(2050+6*(j:ℝ))*(z^2*((3:ℝ)^(8*gammaZero))^j) := by
        convert hh using 1 <;> ring
      _ ≤ _ := by rw [heq]; exact hp'
  have hb := add_le_add hfirst hsecond
  have hv := old_signed_full64_variance_cap M h n hg hstate
  have hcontrol := old_signed_mean_source_cap_decay M h n j
  have hbrace : 0≤3*C+(3/2500)*z^2*C^2*F := by positivity
  have hscaled := hcontrol.trans (mul_le_mul_of_nonneg_right hv hbrace)
  have hfinal := mul_le_mul_of_nonneg_left hb
    (mul_nonneg hθ (by norm_num : (0:ℝ)≤383/250000))
  dsimp [oldSignedMeanSlopeMajorant]
  exact hscaled.trans (by convert hfinal using 1; ring)

/-- The leading source cell has a certified slope below 0.02 theta. -/
theorem old_signed_mean_source_five_cap (M : ABKModel 2) (h : ℝ) (n : ℤ)
    (hg : M.gamma≤gammaZero) (hstate : nativeInductionState M h n) :
    oldSignedMeanSourceCap M h n 5 ≤ theta M*(1/50) := by
  have hh := old_signed_mean_source_majorant M h n hg hstate 0
  apply hh.trans (mul_le_mul_of_nonneg_left ?_ (cold_theta_pos M).le)
  norm_num [oldSignedMeanSlopeMajorant]

end
end ASDExplicitGamma.Native
