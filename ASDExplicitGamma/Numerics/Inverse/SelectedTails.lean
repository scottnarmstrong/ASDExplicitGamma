module
public import ASDExplicitGamma.Numerics.Inverse.RealBounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! The complete selected-height probability tail. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Inverse

/-- A supergeometric height tail is bounded by its complete geometric majorant. -/
theorem inv_selected_probability_tail (x r : ℝ) (hx : 10000 ≤ x) (hr : 13/10 ≤ r) :
    (∑' n : ℕ, Real.exp (-x*r^n)) ≤ (1000/999)*Real.exp (-x) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hr0 : -1 ≤ r := le_trans (by norm_num) hr
  have hc : 1000 ≤ x*(r-1) := by nlinarith only [hx, hr]
  have hc0 : 0 < x*(r-1) := lt_of_lt_of_le (by norm_num) hc
  have he : Real.exp (-(x*(r-1))) ≤ (1/1000 : ℝ) := by
    have h := inv_exp_neg_factorial_bound (x*(r-1)) hc0 1
    norm_num only [Nat.factorial, Nat.cast_one, pow_one] at h
    exact h.trans (one_div_le_one_div_of_le (by norm_num) hc)
  have hmajor (n : ℕ) : Real.exp (-x*r^n) ≤ Real.exp (-x)*(1/1000 : ℝ)^n := by
    have hb := one_add_mul_sub_le_pow hr0 n
    calc
      Real.exp (-x*r^n) ≤ Real.exp (-x+((n : ℝ)*(-(x*(r-1))))) := by
        apply Real.exp_le_exp.mpr
        nlinarith only [mul_le_mul_of_nonneg_left hb hx0.le]
      _ = Real.exp (-x)*Real.exp (-(x*(r-1)))^n := by
        rw [Real.exp_add, Real.exp_nat_mul]
      _ ≤ Real.exp (-x)*(1/1000 : ℝ)^n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.exp_pos _).le he n)
          (Real.exp_pos _).le
  have hg := (hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1/1000 : ℝ)‖ < 1)).mul_left
    (Real.exp (-x))
  have hs := hg.summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) hmajor
  calc
    (∑' n : ℕ, Real.exp (-x*r^n)) ≤ ∑' n : ℕ, Real.exp (-x)*(1/1000 : ℝ)^n :=
      hs.tsum_le_tsum hmajor hg.summable
    _ = (1000/999)*Real.exp (-x) := by
      rw [hg.tsum_eq]
      norm_num
      ring

theorem inv_selected_indices :
    (344-333+1 : ℕ) = 12 ∧ (388-377+1 : ℕ) = 12 ∧
    (344/4-40 : ℚ) = 46 ∧ (388/4-40 : ℚ) = 57 ∧
    (3^46/32 : ℚ) > 10000 ∧ (3^57/32 : ℚ) > 10000 := by
  decide +kernel

theorem inv_quarter_growth : (13/10 : ℝ) < (3 : ℝ)^(1/4 : ℝ) := by
  have h := inv_root_lower (l := 13/10) (x := 3) (n := 4)
    (by decide +kernel) (by decide) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, one_div] at h
  exact h

/-- Infinite global selected tail starts at h=345, whose argument is 3^46/32. -/
theorem inv_global_selected_probability_tail :
    (∑' n : ℕ, Real.exp (-(3^46/32 : ℝ)*((3 : ℝ)^(1/4 : ℝ))^n)) ≤
      (1000/999)*Real.exp (-(3^46/32 : ℝ)) :=
  inv_selected_probability_tail _ _ (by norm_num) inv_quarter_growth.le

/-- Infinite local/full selected tail starts at h=389. -/
theorem inv_local_selected_probability_tail :
    (∑' n : ℕ, Real.exp (-(3^57/32 : ℝ)*((3 : ℝ)^(1/4 : ℝ))^n)) ≤
      (1000/999)*Real.exp (-(3^57/32 : ℝ)) :=
  inv_selected_probability_tail _ _ (by norm_num) inv_quarter_growth.le

end ASDExplicitGamma.Numerics.Inverse
