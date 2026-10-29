module

public import ASDExplicitGamma.Numerics.Scalar.Frames
public import ASDExplicitGamma.Statements.ShellVarianceSum

/-! The actual long-block shell clock, with simple rational bounds inside the certified signal gates. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Numerics

/-- A short Taylor enclosure suffices for the lower clock endpoint. -/
theorem signal_exp_lower : (2108/1000 : ℝ) < Real.exp (74589/100000 : ℝ) := by
  refine lt_of_lt_of_le ?_ (le_exp_of_poly (n := 10) (by norm_num) (by norm_num) le_rfl)
  norm_num [expPoly,expErr,Finset.sum_range_succ,Nat.factorial,abs_of_pos]

/-- A short Taylor enclosure suffices for the upper clock endpoint. -/
theorem signal_exp_upper : Real.exp (187/250 : ℝ) < (2113/1000 : ℝ) := by
  refine lt_of_le_of_lt (exp_le_of_poly (n := 10) (by norm_num) (by norm_num) le_rfl) ?_
  norm_num [expPoly,expErr,Finset.sum_range_succ,Nat.factorial,abs_of_pos]

/-- The all-gamma clock ratio over the source floor length. -/
theorem signal_clock_ratio (gamma : ℝ) (hg : 0 < gamma) (hgmax : gamma ≤ 17/50000) :
    (2108/1000 : ℝ) < (3:ℝ)^(2*gamma*(⌊(17/50:ℝ)/gamma⌋:ℝ)) ∧
      (3:ℝ)^(2*gamma*(⌊(17/50:ℝ)/gamma⌋:ℝ)) < (2113/1000:ℝ) := by
  obtain ⟨hl,hu⟩ := Numerics.Scalar.frame_floor_bounds gamma hg hgmax
  have hp : 0 < gamma*(⌊(17/50:ℝ)/gamma⌋:ℝ) := by linarith only [hl]
  have hlog := Numerics.Scalar.log_three_small
  have hlow := mul_lt_mul_of_pos_left hlog.1 hp
  have hhi := mul_lt_mul_of_pos_left hlog.2 hp
  have hargl : (74589/100000:ℝ) < Real.log 3*(2*gamma*(⌊(17/50:ℝ)/gamma⌋:ℝ)) := by
    nlinarith only [hl,hlow]
  have hargu : Real.log 3*(2*gamma*(⌊(17/50:ℝ)/gamma⌋:ℝ)) < (187/250:ℝ) := by
    nlinarith only [hu,hhi]
  rw [Real.rpow_def_of_pos (by norm_num)]
  exact ⟨signal_exp_lower.trans (Real.exp_lt_exp.mpr hargl),
    (Real.exp_lt_exp.mpr hargu).trans signal_exp_upper⟩

/-- The frozen accumulated variance obeys the exact integer-label multiplicative clock. -/
theorem shellVarianceSum_add (h gamma : ℝ) (n L : ℤ) :
    shellVarianceSum h gamma (n+L) = (3:ℝ)^(2*gamma*(L:ℝ))*shellVarianceSum h gamma n := by
  unfold shellVarianceSum
  rw [Int.cast_add,mul_add,Real.rpow_add (by norm_num : (0:ℝ)<3)]
  ring

end ASDExplicitGamma.Scalar
