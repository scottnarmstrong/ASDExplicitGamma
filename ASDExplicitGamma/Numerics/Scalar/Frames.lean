module

public import ASDExplicitGamma.Numerics.Scalar.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Floor.Ring

/-! Scalar frame-factor and floor endpoints from E1 R15–R16. -/

@[expose] public section
namespace ASDExplicitGamma.Numerics.Scalar

/-- NU-SC-FRAME-FACTOR: the geometric exponential majorant. -/
theorem one_shell_factor :
    (3 : ℝ) ^ (2 * (17/50000 : ℝ)) - 1 ≤
      ((11/5 : ℝ)*(17/50000))/(1-(11/5 : ℝ)*(17/50000)) ∧
    (3 : ℝ) ^ (2 * (17/50000 : ℝ)) < 1251/1250 := by
  have hlog := twice_log_three_lt
  have ha : (2*(17/50000 : ℝ))*Real.log 3 ≤ (11/5)*(17/50000) := by
    linarith only [hlog]
  have hpow : (3 : ℝ)^(2*(17/50000 : ℝ)) ≤
      1/(1-(11/5 : ℝ)*(17/50000)) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    have hexp := Real.exp_le_exp.mpr ha
    rw [mul_comm (Real.log 3)]
    exact hexp.trans (Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num))
  constructor <;> linarith only [hpow]

/-- NU-SC-FRAME-COSTS: the all-γ floor endpoints, with no residue restriction. -/
theorem frame_floor_bounds (gamma : ℝ) (hg : 0 < gamma) (hgmax : gamma ≤ 17/50000) :
    (16983/50000 : ℝ) < gamma * (⌊(17/50 : ℝ)/gamma⌋ : ℝ) ∧
      gamma * (⌊(17/50 : ℝ)/gamma⌋ : ℝ) ≤ 17/50 := by
  have hlow := Int.sub_one_lt_floor ((17/50 : ℝ)/gamma)
  have hupp := Int.floor_le ((17/50 : ℝ)/gamma)
  have hl := mul_lt_mul_of_pos_left hlow hg
  have hu := mul_le_mul_of_nonneg_left hupp hg.le
  rw [mul_sub, mul_div_cancel₀ _ (ne_of_gt hg), mul_one] at hl
  rw [mul_div_cancel₀ _ (ne_of_gt hg)] at hu
  exact ⟨by linarith only [hl, hgmax], hu⟩

/-- NU-SC-FRAME-COSTS: the log-scaled interval used by the hyperbolic costs. -/
theorem frame_log_bounds (gamma : ℝ) (hg : 0 < gamma) (hgmax : gamma ≤ 17/50000) :
    0 < gamma * (⌊(17/50 : ℝ)/gamma⌋ : ℝ) * Real.log 3 ∧
      gamma * (⌊(17/50 : ℝ)/gamma⌋ : ℝ) * Real.log 3 < 187/500 := by
  obtain ⟨hl,hu⟩ := frame_floor_bounds gamma hg hgmax
  have hpos : 0 < gamma * (⌊(17/50 : ℝ)/gamma⌋ : ℝ) := by linarith only [hl]
  constructor
  · exact mul_pos hpos (Real.log_pos (by norm_num))
  · have h := mul_lt_mul_of_pos_left log_three_small.2 hpos
    have hh := mul_le_mul_of_nonneg_right hu (by norm_num : (0 : ℝ) ≤ 11/10)
    linarith only [h,hh]

/-- The long-block exponential majorant on its complete source range. -/
theorem three_power_le_geometric (x : ℝ) (hx : 0 ≤ x) (hdom : (11/10 : ℝ)*x < 1) :
    (3 : ℝ)^x ≤ 1/(1-(11/10 : ℝ)*x) := by
  rw [Real.rpow_def_of_pos (by norm_num)]
  have harg : Real.log 3*x ≤ (11/10 : ℝ)*x :=
    mul_le_mul_of_nonneg_right log_three_small.2.le hx
  exact (Real.exp_le_exp.mpr harg).trans
    (Real.exp_bound_div_one_sub_of_interval (mul_nonneg (by norm_num) hx) hdom)

/-- NU-SC-BFLAT-MONOTONE-TAIL: specialize the source energy-tail bound at lag 128. -/
theorem bflat_monotone_tail (B v : ℝ) (hv : 0 < v)
    (htail : B/v ≤ min 2 ((429/175 : ℝ)*(3 : ℝ)^(-128 : ℤ) -
      (7/15 : ℝ)*((3 : ℝ)^(-128 : ℤ))^2)) :
    B ≤ ((429/175 : ℝ)*(3 : ℝ)^(-128 : ℤ))*v := by
  have h := htail.trans (min_le_right _ _)
  have hc : (0 : ℝ) ≤ (7/15 : ℝ)*((3 : ℝ)^(-128 : ℤ))^2 := by positivity
  exact (div_le_iff₀ hv).mp (h.trans (by linarith only [hc]))

/-- NU-SC-UPPER-BARRIER: positivity between the two source endpoints. -/
theorem upper_barrier_positive (z : ℝ) (hl : 37/250 ≤ z) (hu : z ≤ 9/10) :
    0 < 2 * ((13/8 : ℝ)-1)*z-z^2-2*(681/10000 : ℝ)*(1+z)-(681/10000 : ℝ)^2 := by
  have h := mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr hu)
  nlinarith only [h,hl]

end ASDExplicitGamma.Numerics.Scalar
