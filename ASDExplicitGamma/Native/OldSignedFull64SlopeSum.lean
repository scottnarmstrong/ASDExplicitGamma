module

public import ASDExplicitGamma.Native.OldSignedFull64SlopeMajorant

/-! The complete auxiliary OLD max-history slope, with its theta factor. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Cold Algsuperdiff.Section3
noncomputable section

/-- The complete rational geometric and Eulerian sums of the auxiliary row. -/
theorem old_signed_full64_majorant_hasSum :
    HasSum oldSignedFull64SlopeMajorant ((383/250000:ℝ)*
      (120*(251/250)/(1-17/20)+(28/125)*(509/500)*
        (2050/(1-1/10)+6*(1/10)/(1-1/10)^2))) := by
  have h0 := hasSum_geometric_of_norm_lt_one (by norm_num : ‖(17/20:ℝ)‖<1)
  have h1 := hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1/10:ℝ)‖<1)
  have h2 := hasSum_coe_mul_geometric_of_norm_lt_one (by norm_num : ‖(1/10:ℝ)‖<1)
  have hh := ((h0.mul_left (120*(251/250))).add
    (((h1.mul_left 2050).add (h2.mul_left 6)).mul_left ((28/125)*(509/500)))).mul_left (383/250000)
  convert hh using 1
  · funext j
    dsimp [oldSignedFull64SlopeMajorant]
    ring
  · ring

/-- The actual p20 coefficient is nonnegative, with its true physical frame. -/
theorem old_signed_full64_control_nonneg (M : ABKModel 2) (h : ℝ) (n : ℤ) (j : ℕ) :
    0≤oldSignedP20Full64Control M h n j := by
  have hg := M.shellPrefix.gamma_pos.le
  have hp := old_signed_full64_depth_parameters (n-((5+j:ℕ):ℤ)) j
  dsimp only at hp
  dsimp only [oldSignedP20Full64Control]
  rw [hp.1,hp.2.1]
  dsimp [rawTraceRemainderKappaF,rawTraceRemainderB,rawTraceRemainderA,
    rawTraceRemainderMu,rawTraceRemainderH0,rawTraceRemainderD0,
    rawTraceOldFrameP20LocalClock,oldSignedP20Full64Cap,pureFluxCovarianceRho,pureFluxCovarianceDelta]
  positivity

/-- The full actual max-history slope is bounded by 0.49 theta. This is an
auxiliary stronger comparison route, with no assumed derivative or bank bound. -/
theorem old_signed_full64_slope_sum (M : ABKModel 2) (h : ℝ) (n : ℤ)
    (hg : M.gamma≤gammaZero) (hstate : nativeInductionState M h n) :
    Summable (fun j : ℕ => coldHistoryBeta^j*oldSignedP20Full64Control M h n j) ∧
    (1-inverseHistoryDiscount)*(∑' j : ℕ,coldHistoryBeta^j*oldSignedP20Full64Control M h n j) ≤
      (49/100)*theta M := by
  have hθ : 0≤theta M := (cold_theta_pos M).le
  have hm : Summable oldSignedFull64SlopeMajorant := old_signed_full64_majorant_hasSum.summable
  have hmn : 0≤∑' j,oldSignedFull64SlopeMajorant j := by
    apply tsum_nonneg
    intro j
    dsimp [oldSignedFull64SlopeMajorant]
    positivity
  have hu : Summable (fun j : ℕ => coldHistoryBeta^j*oldSignedP20Full64Control M h n j) :=
    Summable.of_nonneg_of_le (fun j => mul_nonneg (pow_nonneg coldHistoryBeta_pos.le j)
      (old_signed_full64_control_nonneg M h n j))
      (old_signed_full64_depth_majorant M h n hg hstate) (hm.mul_left (theta M))
  have hsum := hu.tsum_le_tsum (old_signed_full64_depth_majorant M h n hg hstate)
    (hm.mul_left (theta M))
  rw [tsum_mul_left] at hsum
  have hmajor : (1-inverseHistoryDiscount)*(∑' j,oldSignedFull64SlopeMajorant j)≤49/100 := by
    calc
      _ ≤ (241/1000)*(∑' j,oldSignedFull64SlopeMajorant j) :=
        mul_le_mul_of_nonneg_right old_signed_history_discount_caps.1 hmn
      _ ≤ _ := by rw [old_signed_full64_majorant_hasSum.tsum_eq]
                  simpa only [mul_assoc] using old_signed_full64_slope_numeric
  refine ⟨hu,?_⟩
  have hh := mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr inverse_history_discount_range.2.le)
  have hlast := mul_le_mul_of_nonneg_right hmajor hθ
  calc
    _ ≤ (1-inverseHistoryDiscount)*(theta M*∑' j,oldSignedFull64SlopeMajorant j) := hh
    _ ≤ _ := by
      convert hlast using 1
      ring

end
end ASDExplicitGamma.Native
