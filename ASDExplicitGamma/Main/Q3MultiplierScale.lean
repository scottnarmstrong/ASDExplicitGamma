module

public import ASDExplicitGamma.Main.Q3RemainderCaps
public import ASDExplicitGamma.Main.Q3RowCaps
public import ASDExplicitGamma.Main.Q3ColumnProduct
public import ASDExplicitGamma.Main.ColumnProductCaps
public import ASDExplicitGamma.Triadic.PlanarDirectionOperations

/-! The actual physical scale inequalities yielding the held main-return coefficients. -/

@[expose] public section
namespace ASDExplicitGamma.Main
open Homogenization ASDExplicitGamma.Triadic

/-- Longer physical correlation lengths decrease both derivative moments. -/
theorem main_q3_derivative_moment_antitone {c b L0 L1 : ℝ} (hc : 0 ≤ c)
    (h0 : 0 < L0) (hL : L0 ≤ L1) (k : ℕ) :
    c*b^2/L1^k ≤ c*b^2/L0^k :=
  div_le_div_of_nonneg_left (mul_nonneg hc (sq_nonneg _)) (pow_pos h0 k)
    (pow_le_pow_left₀ h0.le hL k)

/-- The full-column coefficient is monotone in the physical length. -/
theorem mainQ3ColumnConstant_length_antitone {r b L0 L1 : ℝ} (hr : 0 ≤ r)
    (h0 : 0 < L0) (hL : L0 ≤ L1) :
    mainQ3ColumnConstant r b L1 ≤ mainQ3ColumnConstant r b L0 := by
  unfold mainQ3ColumnConstant
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (main_q3_derivative_moment_antitone (by norm_num : (0:ℝ) ≤ 156/5) h0 hL 2))
      (by positivity)
  · exact mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (main_q3_derivative_moment_antitone (by norm_num : (0:ℝ) ≤ 46488/25) h0 hL 4))
      (by positivity)

/-- The residual coefficient is monotone in the physical length. -/
theorem mainQ3RemainderConstant_length_antitone {r b L0 L1 : ℝ} (hr : 0 ≤ r)
    (h0 : 0 < L0) (hL : L0 ≤ L1) :
    mainQ3RemainderConstant r b L1 ≤ mainQ3RemainderConstant r b L0 := by
  unfold mainQ3RemainderConstant
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (main_q3_derivative_moment_antitone (by norm_num : (0:ℝ) ≤ 156/5) h0 hL 2))
      (by positivity)
  · exact mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (main_q3_derivative_moment_antitone (by norm_num : (0:ℝ) ≤ 46488/25) h0 hL 4))
      (by positivity)

/-- Every source-admissible physical length has the held common kd cap. -/
theorem mainQ3ColumnConstant_le_mainKd {r b L : ℝ} (hr : 0 < r) (hL : r*3^6 ≤ L) :
    mainQ3ColumnConstant r b L ≤ mainKd (b^2) := by
  have h := mainQ3ColumnConstant_length_antitone (b := b) hr.le (mul_pos hr (by norm_num)) hL
  rwa [mainQ3ColumnConstant_source hr] at h

/-- Every source-admissible physical length has the held krem cap. -/
theorem mainQ3RemainderConstant_le_mainKrem {r b L : ℝ} (hr : 0 < r) (hL : r*3^6 ≤ L) :
    mainQ3RemainderConstant r b L ≤ mainKrem (b^2) := by
  have h := mainQ3RemainderConstant_length_antitone (b := b) hr.le (mul_pos hr (by norm_num)) hL
  rwa [mainQ3RemainderConstant_source hr] at h

end ASDExplicitGamma.Main
