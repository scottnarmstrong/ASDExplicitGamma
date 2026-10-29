module

public import ASDExplicitGamma.Statements.NativeInductionState
public import ASDExplicitGamma.Model.ShellScaling
public import ASDExplicitGamma.Numerics.Demo

/-! The old-label variance clock, MA-SHELL-CLOCK. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Algsuperdiff.Section3

/-- Point variance of the next shell in the deterministic OLD true frame. -/
noncomputable def shellClock (M : ABKModel 2) (h : ℝ) (m : ℤ) : ℝ :=
  h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * ((m + 1 : ℤ) : ℝ)) /
    (Annealed.sigmaBar M m : ℝ) ^ 2

/-- The exact geometric-shell identity, before using the old-label corridor. -/
theorem shellClock_eq (M : ABKModel 2) (h : ℝ) (m : ℤ) (hγ : 0 < M.gamma) :
    shellClock M h m =
      (1 - (3 : ℝ) ^ (-(2 * M.gamma))) * (3 : ℝ) ^ (2 * M.gamma) *
        shellVarianceSum h M.gamma m / (Annealed.sigmaBar M m : ℝ) ^ 2 := by
  have hden : 1 - (3 : ℝ) ^ (-(2 * M.gamma)) ≠ 0 := by
    have : (3 : ℝ) ^ (-(2 * M.gamma)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith [hγ])
    linarith only [this]
  unfold shellClock shellVarianceSum
  rw [Int.cast_add, Int.cast_one, mul_add, mul_one,
    Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  field_simp

/-- The clock bound consumes component seven at the completed OLD label.
No current-label state or independent clock premise is used. -/
theorem shellClock_le (M : ABKModel 2) (h : ℝ) (m : ℤ)
    (hγ : 0 < M.gamma) (hm : nativeInductionState M h m) :
    shellClock M h m ≤ (443 / 125 : ℝ) * M.gamma * (3 : ℝ) ^ (2 * M.gamma) := by
  have hB : 0 ≤ shellVarianceSum h M.gamma m := by
    unfold shellVarianceSum
    apply div_nonneg (by positivity)
    exact sub_nonneg.mpr (le_of_lt
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith [hγ])))
  have hcorr := hm.2.2.2.2.2.2.1
  have hratio : shellVarianceSum h M.gamma m /
      (Annealed.sigmaBar M m : ℝ) ^ 2 ≤ (50 / 31 : ℝ) := by
    apply (div_le_iff₀ (sq_pos_of_pos (Annealed.sigmaBar M m).2)).mpr
    nlinarith only [hcorr, sq_nonneg M.nu]
  have hclock : 1 - (3 : ℝ) ^ (-(2 * M.gamma)) ≤
      2 * M.gamma * Real.log 3 := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    linarith only [Real.add_one_le_exp (Real.log 3 * -(2 * M.gamma))]
  have hnonneg : 0 ≤ 1 - (3 : ℝ) ^ (-(2 * M.gamma)) := by
    exact sub_nonneg.mpr (le_of_lt
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith [hγ])))
  have hlog : 2 * Real.log 3 * (50 / 31 : ℝ) ≤ (443 / 125 : ℝ) := by
    linarith only [Numerics.demo_clock_margin]
  rw [shellClock_eq M h m hγ, mul_div_assoc]
  calc
    _ ≤ ((1 - (3 : ℝ) ^ (-(2 * M.gamma))) * (3 : ℝ) ^ (2 * M.gamma)) *
        (50 / 31 : ℝ) := mul_le_mul_of_nonneg_left hratio (by positivity)
    _ ≤ (2 * M.gamma * Real.log 3 * (3 : ℝ) ^ (2 * M.gamma)) * (50 / 31 : ℝ) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hclock (by positivity)) (by norm_num)
    _ = (2 * Real.log 3 * (50 / 31 : ℝ)) * M.gamma * (3 : ℝ) ^ (2 * M.gamma) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hlog hγ.le) (by positivity)

end ASDExplicitGamma.Main
