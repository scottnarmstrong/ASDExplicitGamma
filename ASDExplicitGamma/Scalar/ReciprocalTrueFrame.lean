module

public import ASDExplicitGamma.Scalar.ReciprocalInteger
public import ASDExplicitGamma.Scalar.TrueFrameNormalization
public import ASDExplicitGamma.Statements.ShellVarianceSum

/-! Reciprocal conversion in the actual running diffusivity and frozen variance clock. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Algsuperdiff.Section3 Homogenization

/-- The frozen accumulated variance is nonnegative and nondecreasing at every positive exponent. -/
theorem shellVarianceSum_monotone (h gamma : ℝ) (hg : 0<gamma) :
    Monotone (shellVarianceSum h gamma) := by
  have hd : 0<1-(3:ℝ)^(-(2*gamma)) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hg]))
  intro i j hij
  unfold shellVarianceSum
  apply div_le_div_of_nonneg_right _ hd.le
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg h)
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  exact mul_le_mul_of_nonneg_left (Int.cast_le.mpr hij) (by linarith only [hg])

end ASDExplicitGamma.Scalar
