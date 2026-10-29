module

public import ASDExplicitGamma.Statements.NativeInductionState
public import ASDExplicitGamma.Numerics.Scalar.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Physical shell variance is measured in the true frame at the gate label. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Algsuperdiff.Section3

/-- The geometric shell denominator is bounded by its exact exponential clock. -/
theorem wave_variance_clock (γ : ℝ) (hγ : 0 ≤ γ) :
    1 - (3 : ℝ) ^ (-(2 * γ)) ≤ (11 / 5) * γ := by
  have he := Real.add_one_le_exp (-(2 * γ) * Real.log 3)
  have hr : (3 : ℝ) ^ (-(2 * γ)) = Real.exp (-(2 * γ) * Real.log 3) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    congr 1
    ring
  rw [← hr] at he
  have hl := mul_le_mul_of_nonneg_left Numerics.Scalar.log_three_small.2.le
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hγ)
  linarith only [he, hl]

/-- The native lower corridor supplies the quarter-variance premise at the
actual gate label, with its true scalar sigmaBar. -/
theorem wave_gate_lower_corridor (M : ABKModel 2) (h : ℝ) (j : ℤ)
    (hj : nativeInductionState M h j) :
    shellVarianceSum h M.gamma j / 4 ≤ (Annealed.sigmaBar M j : ℝ) ^ 2 := by
  obtain ⟨_, _, _, _, _, _, hl, _⟩ := hj
  have hg := M.shellPrefix.gamma_pos
  have hd : 0 < 1 - (3 : ℝ) ^ (-(2 * M.gamma)) := by
    have hh := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 3)
      (by linarith only [hg] : -(2 * M.gamma) < 0)
    linarith only [hh]
  have hB : 0 ≤ shellVarianceSum h M.gamma j := by
    unfold shellVarianceSum
    exact div_nonneg (by positivity) hd.le
  linarith only [hl, hB, sq_nonneg M.nu]

/-- A physical shell above a completed gate is normalized by that gate's true
frame. The factor nine is the source variance budget, not a new scalar frame. -/
theorem wave_normalized_shell_variance_of_lower (M : ABKModel 2) (h : ℝ) (j L : ℤ)
    (hLower : shellVarianceSum h M.gamma j / 4 ≤ (Annealed.sigmaBar M j : ℝ)^2) :
    h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * ((j + L : ℤ) : ℝ)) /
      (Annealed.sigmaBar M j : ℝ) ^ 2 ≤
        9 * M.gamma * (3 : ℝ) ^ (2 * M.gamma * (L : ℝ)) := by
  let B := shellVarianceSum h M.gamma j
  let d := 1 - (3 : ℝ) ^ (-(2 * M.gamma))
  let v := h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ))
  have hγ := M.shellPrefix.gamma_pos
  have hd : 0 < d := by
    have hh := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 3)
      (by linarith only [hγ] : -(2 * M.gamma) < 0)
    exact sub_pos.mpr hh
  have hB : B = v / d := rfl
  have hv : 0 ≤ v := by positivity
  have hs : 0 < (Annealed.sigmaBar M j : ℝ) :=
    (Annealed.sigmaBar_characterization M j).1
  have hBs := hLower
  change B / 4 ≤ (Annealed.sigmaBar M j : ℝ) ^ 2 at hBs
  have hvbound : v ≤ 4 * d * (Annealed.sigmaBar M j : ℝ) ^ 2 := by
    rw [hB] at hBs
    have hh := (div_le_iff₀ hd).mp (show v / d ≤ 4 * (Annealed.sigmaBar M j : ℝ) ^ 2 by linarith only [hBs])
    nlinarith only [hh]
  have hc : d ≤ (11 / 5) * M.gamma := wave_variance_clock M.gamma hγ.le
  have hr : v / (Annealed.sigmaBar M j : ℝ) ^ 2 ≤ 9 * M.gamma := by
    apply (div_le_iff₀ (sq_pos_of_pos hs)).mpr
    have hh := mul_le_mul_of_nonneg_right hc (sq_nonneg (Annealed.sigmaBar M j : ℝ))
    nlinarith only [hvbound, hh, mul_nonneg hγ.le (sq_nonneg (Annealed.sigmaBar M j : ℝ))]
  have he : h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * ((j + L : ℤ) : ℝ)) =
      v * (3 : ℝ) ^ (2 * M.gamma * (L : ℝ)) := by
    rw [Int.cast_add, mul_add, Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    exact (mul_assoc _ _ _).symm
  rw [he, mul_div_right_comm]
  exact mul_le_mul_of_nonneg_right hr (Real.rpow_pos_of_pos (by norm_num) _).le

end ASDExplicitGamma.Gaussian
