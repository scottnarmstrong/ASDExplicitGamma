module

public import ASDExplicitGamma.Triadic.PlanarConstants
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Kernel-checked sharp weak-face and Bernstein certificates. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

noncomputable section

/-- Squared positive-Haar norm of the centered unit-cell coordinate. -/
def diagWeakFaceVariance : ℝ := 2 * Real.sqrt 3 / (3 * (9 - Real.sqrt 3))

theorem diagWeakFaceVariance_pos : 0 < diagWeakFaceVariance := by
  have h0 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hs : Real.sqrt 3 < 9 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  unfold diagWeakFaceVariance
  positivity

theorem diagWeakFaceVariance_nonneg : 0 ≤ diagWeakFaceVariance := by
  have hs : Real.sqrt 3 < 9 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  unfold diagWeakFaceVariance
  positivity

/-- The exact weak-face variance is strictly below one quarter. -/
theorem diagWeakFaceVariance_lt_quarter : diagWeakFaceVariance < 1 / 4 := by
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hs : Real.sqrt 3 < 9 := by nlinarith only [hsq]
  unfold diagWeakFaceVariance
  apply (div_lt_iff₀ (by positivity : 0 < 3 * (9 - Real.sqrt 3))).2
  nlinarith only [hsq]

/-- The strict rational enclosure used in both multiplier certificates. -/
theorem diagPlanarC1_sq_lt_tenth : planarC1 ^ 2 < 1 / 10 := by
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hs0 := Real.sqrt_nonneg (3 : ℝ)
  have hs : Real.sqrt 3 < 7 / 4 := by nlinarith only [hsq, hs0]
  have hp : (31 / 10 : ℝ) < Real.pi := by linarith only [Real.pi_gt_d2]
  have hpi : (961 / 100 : ℝ) < Real.pi ^ 2 := by nlinarith only [hp, Real.pi_pos]
  have htail : (29 / 36 : ℝ) < 1 - Real.sqrt 3 / 9 := by linarith only [hs]
  have hden : (961 / 100 : ℝ) * (29 / 36) < Real.pi ^ 2 * (1 - Real.sqrt 3 / 9) :=
    mul_lt_mul hpi htail.le (by norm_num) (by positivity)
  rw [planarC1_sq]
  apply (div_lt_iff₀ (by positivity : 0 < Real.pi ^ 2 * (1 - Real.sqrt 3 / 9))).2
  nlinarith only [hs, hden]

end

end ASDExplicitGamma.Triadic
