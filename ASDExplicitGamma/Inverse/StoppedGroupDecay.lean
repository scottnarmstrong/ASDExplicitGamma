module

public import ASDExplicitGamma.Inverse.StoppedGroupVolume

/-! The actual ceil(k/3) stopped profile and valid support volume leave the
summable 3^(-k/6) L2 envelope. This is independent of response estimates. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory
noncomputable section

def rootGroupClock (H a : ℕ) : ℝ := (3:ℝ)^(((a+whitneyProfile H a:ℕ):ℝ)/4)

def groupClockBound (H : ℕ) : ℝ := (3:ℝ)^(((H:ℝ)+4)/4)

def groupGeometricRatio : ℝ := (3:ℝ)^(-1/6:ℝ)

theorem group_clock_weighted_bound (H a : ℕ) :
    rootGroupClock H a*(3:ℝ)^(-(a:ℝ)/2) ≤ groupClockBound H*groupGeometricRatio^a := by
  have hc : 3*((a+2)/3) ≤ a+2 := by omega
  have hcR : 3*(((a+2)/3:ℕ):ℝ) ≤ (a:ℝ)+2 := by exact_mod_cast hc
  have he : (((a+whitneyProfile H a:ℕ):ℝ)/4)-(a:ℝ)/2 ≤ ((H:ℝ)+4)/4-(a:ℝ)/6 := by
    simp only [whitneyProfile,Nat.cast_add,Nat.cast_ofNat]
    linarith only [hcR]
  unfold rootGroupClock groupClockBound groupGeometricRatio
  rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 3),
    ← Real.rpow_add (by norm_num : (0:ℝ) < 3),← Real.rpow_add (by norm_num : (0:ℝ) < 3)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3)
  nlinarith only [he]

/-- The exact support-volume square root has the source half-exponent. -/
theorem group_support_sqrt_bound (Q : TriadicCube 2) (a : ℕ) :
    Real.sqrt (rootGroupVolumeBudget Q a) ≤
      4*Real.sqrt ((volume (cubeSet Q)).toReal)*(3:ℝ)^(-(a:ℝ)/2) := by
  have hp : ((3:ℝ)^(-(a:ℝ)/2))^2 = (1/3:ℝ)^a := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3),Nat.cast_ofNat,
      show (-(a:ℝ)/2)*(2:ℝ) = -(a:ℝ) by ring,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 3),Real.rpow_natCast]
    simp only [one_div,inv_pow]
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have he : (4*Real.sqrt ((volume (cubeSet Q)).toReal)*(3:ℝ)^(-(a:ℝ)/2))^2 =
        rootGroupVolumeBudget Q a := by
      rw [mul_pow,mul_pow,Real.sq_sqrt ENNReal.toReal_nonneg,hp]
      unfold rootGroupVolumeBudget
      ring
    exact he.symm.le

/-- The complete physical clock times the square-root volume has a single
geometric majorant, without a finite layer truncation. -/
theorem group_clock_volume_bound (Q : TriadicCube 2) (H a : ℕ) :
    rootGroupClock H a*Real.sqrt (rootGroupVolumeBudget Q a) ≤
      (4*Real.sqrt ((volume (cubeSet Q)).toReal)*groupClockBound H)*groupGeometricRatio^a := by
  apply (mul_le_mul_of_nonneg_left (group_support_sqrt_bound Q a)
    (show 0 ≤ rootGroupClock H a by unfold rootGroupClock; positivity)).trans
  have hh := mul_le_mul_of_nonneg_left (group_clock_weighted_bound H a)
    (show 0 ≤ 4*Real.sqrt ((volume (cubeSet Q)).toReal) by positivity)
  simpa only [mul_assoc,mul_left_comm,mul_comm] using hh

/-- Complete L2 fallback summability, before the global map is constructed. -/
theorem group_clock_volume_summable (Q : TriadicCube 2) (H : ℕ) :
    Summable (fun a : ℕ => rootGroupClock H a*Real.sqrt (rootGroupVolumeBudget Q a)) := by
  have hr0 : 0 ≤ groupGeometricRatio := by unfold groupGeometricRatio; positivity
  have hr1 : groupGeometricRatio < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1:ℝ) < 3) (by norm_num : (-1/6:ℝ) < 0)
  have hs := (hasSum_geometric_of_lt_one hr0 hr1).summable.mul_left
    (4*Real.sqrt ((volume (cubeSet Q)).toReal)*groupClockBound H)
  exact Summable.of_nonneg_of_le (fun a => by unfold rootGroupClock; positivity)
    (group_clock_volume_bound Q H) hs

end
end ASDExplicitGamma.Inverse
