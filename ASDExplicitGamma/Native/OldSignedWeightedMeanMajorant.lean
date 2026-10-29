module

public import ASDExplicitGamma.Native.OldSignedWeightedMeanRatios

/-! Complete geometric majorants of inverse-weighted source mean slopes. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Gaussian Scalar Inverse Cold Algsuperdiff.Section3
noncomputable section

def oldSignedWeightedMeanSlopeMajorant (j : ℕ) : ℝ :=
  (383/250000)*(3*(251/250)*(29/50:ℝ)^j+
    (3/625)*(509/500)*(2050+6*(j:ℝ))*(13/200:ℝ)^j)

/-- Exact combination of the rational depth-weight and mean-slope profiles. -/
theorem old_signed_weighted_mean_majorant_scalar (j : ℕ) :
    ((289/500:ℝ)*(1001/1000))^j*oldSignedMeanSlopeMajorant j ≤
      oldSignedWeightedMeanSlopeMajorant j := by
  have h1 := pow_le_pow_left₀
    (by norm_num : (0:ℝ)≤((289/500)*(1001/1000))*(1001/1000))
    (by norm_num : ((289/500:ℝ)*(1001/1000))*(1001/1000)≤29/50) j
  have h2 := pow_le_pow_left₀
    (by norm_num : (0:ℝ)≤((289/500)*(1001/1000))*(14/125))
    (by norm_num : ((289/500:ℝ)*(1001/1000))*(14/125)≤13/200) j
  rw [mul_pow] at h1 h2
  have hh1 := mul_le_mul_of_nonneg_left h1 (by norm_num : (0:ℝ)≤3*(251/250))
  have hh2 := mul_le_mul_of_nonneg_left h2
    (by positivity : (0:ℝ)≤(3/625)*(509/500)*(2050+6*(j:ℝ)))
  have hh := mul_le_mul_of_nonneg_left (add_le_add hh1 hh2)
    (by norm_num : (0:ℝ)≤383/250000)
  convert hh using 1
  · dsimp [oldSignedMeanSlopeMajorant]; ring
  · rfl

/-- Every actual weighted source coefficient has a fixed summable majorant. -/
theorem old_signed_weighted_mean_source_majorant (M : ABKModel 2) (h : ℝ) (n : ℤ)
    (hg : M.gamma≤gammaZero) (hstate : nativeInductionState M h n) (j : ℕ) :
    inverseHistoryDiscount^(2*j)*bankDepthFrame M j*oldSignedMeanSourceCap M h n (5+j) ≤
      theta M*oldSignedWeightedMeanSlopeMajorant j := by
  let w := inverseHistoryDiscount^(2*j)*bankDepthFrame M j
  let R := ((289/500:ℝ)*(1001/1000))^j
  have hθ := (cold_theta_pos M).le
  have hw : 0≤w := mul_nonneg (pow_nonneg inverse_history_discount_range.1.le _)
    (by unfold bankDepthFrame; positivity)
  have hmaj : 0≤oldSignedMeanSlopeMajorant j := by dsimp [oldSignedMeanSlopeMajorant]; positivity
  have hcap := mul_le_mul_of_nonneg_left
    (old_signed_mean_source_majorant M h n hg hstate j) hw
  have hweight := mul_le_mul_of_nonneg_right (old_signed_weighted_mean_depth_weight M hg j)
    (mul_nonneg hθ hmaj)
  have hfinal := mul_le_mul_of_nonneg_left (old_signed_weighted_mean_majorant_scalar j) hθ
  calc
    _ ≤ w*(theta M*oldSignedMeanSlopeMajorant j) := hcap
    _ ≤ R*(theta M*oldSignedMeanSlopeMajorant j) := hweight
    _ ≤ _ := by convert hfinal using 1; ring

/-- The two complete sums are geometric and affine-geometric, respectively. -/
theorem old_signed_weighted_mean_majorant_hasSum :
    HasSum oldSignedWeightedMeanSlopeMajorant ((383/250000:ℝ)*
      (3*(251/250)/(1-29/50)+(3/625)*(509/500)*
        (2050/(1-13/200)+6*(13/200)/(1-13/200)^2))) := by
  have h0 := hasSum_geometric_of_norm_lt_one (by norm_num : ‖(29/50:ℝ)‖<1)
  have h1 := hasSum_geometric_of_norm_lt_one (by norm_num : ‖(13/200:ℝ)‖<1)
  have h2 := hasSum_coe_mul_geometric_of_norm_lt_one (by norm_num : ‖(13/200:ℝ)‖<1)
  have hh := ((h0.mul_left (3*(251/250))).add
    (((h1.mul_left 2050).add (h2.mul_left 6)).mul_left ((3/625)*(509/500)))).mul_left (383/250000)
  convert hh using 1
  · funext j
    dsimp [oldSignedWeightedMeanSlopeMajorant]
    ring
  · ring

end
end ASDExplicitGamma.Native
