module

public import ASDExplicitGamma.Numerics.Enclosures
import Mathlib.Tactic.Linarith

/-! Elementary scalar numeric obligations from Part B. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.Scalar

/-- NU-SC-H-SOURCE: fourth-power source-history margin. -/
theorem source_history_fourth_power :
    (5423 / 2500 : ℚ) ^ 4 > 27 * (2379 / 2500 : ℚ) ^ 4 := by
  decide +kernel

/-- NU-SC-LOG3-SMALL: the existing independently proved log enclosure suffices. -/
theorem log_three_small :
    (549 / 500 : ℝ) < Real.log 3 ∧ Real.log 3 < 11 / 10 := by
  obtain ⟨hl, hu⟩ := log_three_enclosure
  constructor <;> linarith only [hl, hu]

/-- NU-SC-LOG3-UPPER: the one-shell clock comparison. -/
theorem twice_log_three_lt : 2 * Real.log 3 < (11 / 5 : ℝ) := by
  linarith only [log_three_small.2]

/-- NU-SC-CLOCKS: retain enough precision for the tight main clock. -/
theorem lower_clock_margins :
    (443 / 125 : ℝ) * (31 / 50) > 2 * Real.log 3 ∧
      (9 / 2 : ℝ) * (49 / 100) > 2 * Real.log 3 := by
  have hu := log_three_enclosure.2
  constructor <;> linarith only [hu]

/-- NU-SC-FRAME-RATIOS: the restored-frame endpoint constants. -/
theorem frame_ratio_constants : (65 / 22 : ℝ) < 3 ∧ Real.sqrt 3 < 2 := by
  constructor
  · norm_num
  · exact (Real.sqrt_lt' (by norm_num)).2 (by norm_num)

/-- NU-SC-UPPER-STARTUP: the molecular five-four comparison. -/
theorem molecular_startup (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    (1 + x / 2) ^ 2 ≤ 1 + 5 * x / 4 := by
  have h := mul_nonneg hx (sub_nonneg.mpr hx1)
  nlinarith only [h]

/-- NU-SC-OLD-GROUPED-REMAINDER: the exact global population comparison. -/
theorem global_group_population : (9 : ℕ) ^ 89 < 5 ^ 128 := by
  decide +kernel

/-- NU-SC-OLD-GROUPED-REMAINDER: the local charge stays distinct from the global one. -/
theorem grouped_error_values :
    5 * (1 / 10 ^ 24 : ℚ) = 5 / 10 ^ 24 ∧
      5 * (3 / 10 ^ 46 : ℚ) = 15 / 10 ^ 46 := by
  decide +kernel

/-- NU-SC-BRIDGE-RESERVE: the two independent rational reserve comparisons. -/
theorem bridge_reserve_arithmetic :
    2 * 12 * 10 ^ 6 * 225 * (1 / 10 ^ 24 : ℚ) = 54 / 10 ^ 16 ∧
      (54 / 10 ^ 16 : ℚ) < 1 / 10 ^ 12 ∧
      (27 / 10 ^ 15 : ℚ) < 1 / 10 ^ 12 := by
  decide +kernel

/-- The concave squared barrier used in NU-SC-UPPER-BARRIER. -/
def upperBarrier (z : ℚ) : ℚ :=
  2 * (13 / 8 - 1) * z - z ^ 2 - 2 * (681 / 10000) * (1 + z) - (681 / 10000) ^ 2

/-- NU-SC-UPPER-BARRIER: exact endpoint values and their positive margins. -/
theorem upper_barrier_endpoints :
    upperBarrier (37 / 250) = 210079 / 10 ^ 8 ∧
      upperBarrier (9 / 10) = 5158239 / 10 ^ 8 ∧
      (0 : ℚ) < 210079 / 10 ^ 8 ∧ (0 : ℚ) < 5158239 / 10 ^ 8 := by
  decide +kernel

end ASDExplicitGamma.Numerics.Scalar
