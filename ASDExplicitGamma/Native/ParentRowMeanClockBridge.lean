module

public import ASDExplicitGamma.Native.ParentRowMeanSlopeValue
public import ASDExplicitGamma.Native.ParentBoundaryMeanSlope

/-! Exact identification of the primitive source-mean clocks with the parent program clocks. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Gaussian Algsuperdiff.Section3
noncomputable section

/-- The primitive source variance is the same finite clock used by the parent setup. -/
theorem parent_row_mean_variance_eq (height : ℕ) :
    parentBoundaryCommonSourceVariance gammaZero height=parentRowVarianceClock height := by
  unfold parentBoundaryCommonSourceVariance parentRowVarianceClock
  exact Fin.sum_univ_eq_sum_range (fun k => nativeSourceShellClock gammaZero (k+1)) height

/-- Even spatial powers retain exactly their mesh-five weighted shell clocks. -/
theorem parent_row_mean_spatial_eq (height p : ℕ) :
    parentBoundaryCommonSourceSpatialClock gammaZero height 5 (2*p)=
      parentRowWeightedClock (fun k => (1/9)^(p*(k+6))) height := by
  unfold parentBoundaryCommonSourceSpatialClock parentRowWeightedClock
  change (∑ i : Fin height,(fun k : ℕ => nativeSourceShellClock gammaZero (k+1)*
    (1/3:ℝ)^((5+(k+1))*(2*p))) i.val)=_
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => nativeSourceShellClock gammaZero (k+1)*
    (1/3:ℝ)^((5+(k+1))*(2*p))) height]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  simp only [Rat.cast_pow,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat]
  rw [show (5+(i+1))*(2*p)=2*(p*(i+6)) by ring,pow_mul]
  norm_num

/-- The actual A2 source clock is the exact setup derivative clock. -/
theorem parent_row_mean_a2_eq (height : ℕ) :
    parentBoundaryCommonSourceSpatialClock gammaZero height 5 2=
      parentRowWeightedClock parentRowA2Weight height := by
  change parentBoundaryCommonSourceSpatialClock gammaZero height 5 2=
    parentRowWeightedClock (fun k => (1/9)^(k+6)) height
  simpa only [Nat.mul_one,Nat.one_mul] using
    parent_row_mean_spatial_eq height 1

/-- The actual A4 source clock is the exact setup fourth-order clock. -/
theorem parent_row_mean_a4_eq (height : ℕ) :
    parentBoundaryCommonSourceSpatialClock gammaZero height 5 4=
      parentRowWeightedClock parentRowA4Weight height := by
  exact parent_row_mean_spatial_eq height 2

/-- The stored rational raw base is exactly the primitive full-response base. -/
theorem parent_row_mean_raw_base_eq (height : ℕ) :
    parentBoundaryCommonRawBase gammaZero height 5=(parentRowRawBase height:ℝ) := by
  unfold parentBoundaryCommonRawBase parentRowRawBase gammaZero
  push_cast
  ring

/-- The primitive full-response frame is the exact exponential in the source program. -/
theorem parent_row_mean_raw_factor_eq (height : ℕ) :
    parentBoundaryCommonRawFactor gammaZero height 5=
      Real.exp (Real.log 3*((17/50000)*(2*(height:ℝ)+24)))*4 := by
  unfold parentBoundaryCommonRawFactor gammaZero
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3)]
  rw [mul_comm]
  congr 1
  congr 1
  norm_num
  ring

end
end ASDExplicitGamma.Native
