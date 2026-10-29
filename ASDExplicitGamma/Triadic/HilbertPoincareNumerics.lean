module

public import ASDExplicitGamma.Triadic.HilbertPoincareNorms
public import Mathlib.Analysis.Real.Pi.Bounds

/-! Certified decimal enclosures for the displayed quarter-order constants. -/

@[expose] public section
namespace ASDExplicitGamma.Triadic
noncomputable section

 theorem haarPoincareM_quarter : Real.sqrt (haarPoincareM2 ((3:ℝ)^(2*(1/4:ℝ)))) = planarC1 := by
  rw [haarPoincareM2_quarter]
  exact Real.sqrt_sq (show 0 ≤ planarC1 from Real.sqrt_nonneg _)

private theorem quarter_denominator_bounds :
    (9-(1.732050807568878:ℝ))*(3.141592653589793:ℝ)^2 ≤ (9-Real.sqrt 3)*Real.pi^2 ∧
    (9-Real.sqrt 3)*Real.pi^2 ≤ (9-(1.732050807568877:ℝ))*(3.141592653589794:ℝ)^2 := by
  have ht : (1.732050807568877:ℝ) ≤ Real.sqrt 3 ∧ Real.sqrt 3 ≤ (1.732050807568878:ℝ) := by
    constructor
    · nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg (3:ℝ)]
    · nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg (3:ℝ)]
  have hp : (3.141592653589793:ℝ) ≤ Real.pi ∧ Real.pi ≤ (3.141592653589794:ℝ) := by
    constructor
    · linarith only [Real.pi_gt_d20]
    · linarith only [Real.pi_lt_d20]
  constructor
  · exact mul_le_mul (by linarith only [ht.2]) (pow_le_pow_left₀ (by norm_num) hp.1 2)
      (by norm_num) (by nlinarith only [ht.2])
  · exact mul_le_mul (by linarith only [ht.1]) (pow_le_pow_left₀ Real.pi_pos.le hp.2 2)
      (sq_nonneg _) (by norm_num)

/-- The displayed c0 decimal is certified by an interval of width 2e-9. -/
theorem planarC0_decimal_bounds : (0.439510740:ℝ) < planarC0 ∧ planarC0 < (0.439510742:ℝ) := by
  have hd := quarter_denominator_bounds
  have ht : (1.732050807568877:ℝ) ≤ Real.sqrt 3 ∧ Real.sqrt 3 ≤ (1.732050807568878:ℝ) := by
    constructor <;> nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg (3:ℝ)]
  have hdpos : 0 < (9-Real.sqrt 3)*Real.pi^2 := lt_of_lt_of_le (by norm_num) hd.1
  have he : planarC0^2*((9-Real.sqrt 3)*Real.pi^2) = 8*Real.sqrt 3 := by
    rw [planarC0_sq]; exact div_mul_cancel₀ _ hdpos.ne'
  have hl := mul_le_mul_of_nonneg_left hd.1 (sq_nonneg planarC0)
  have hu := mul_le_mul_of_nonneg_left hd.2 (sq_nonneg planarC0)
  have hslo : (0.439510740:ℝ)^2 < planarC0^2 := by nlinarith only [he, hu, ht.1]
  have hshi : planarC0^2 < (0.439510742:ℝ)^2 := by nlinarith only [he, hl, ht.2]
  constructor <;> nlinarith only [hslo, hshi, show 0 ≤ planarC0 from Real.sqrt_nonneg _]

/-- The displayed c1 decimal is certified by an interval of width 2e-10. -/
theorem planarC1_decimal_bounds : (0.3030651874:ℝ) < planarC1 ∧ planarC1 < (0.3030651876:ℝ) := by
  have hd := quarter_denominator_bounds
  have ht : (1.732050807568877:ℝ) ≤ Real.sqrt 3 ∧ Real.sqrt 3 ≤ (1.732050807568878:ℝ) := by
    constructor <;> nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg (3:ℝ)]
  have hdpos : 0 < (9-Real.sqrt 3)*Real.pi^2 := lt_of_lt_of_le (by norm_num) hd.1
  have he : planarC1^2*((9-Real.sqrt 3)*Real.pi^2) = 9*(Real.sqrt 3-1) := by
    rw [planarC1_sq]
    have hratio : 1-Real.sqrt 3/9 ≠ 0 := by nlinarith only [ht.2]
    have ht9 : 9-Real.sqrt 3 ≠ 0 := by nlinarith only [ht.2]
    field_simp [Real.pi_ne_zero, hratio, ht9]
  have hl := mul_le_mul_of_nonneg_left hd.1 (sq_nonneg planarC1)
  have hu := mul_le_mul_of_nonneg_left hd.2 (sq_nonneg planarC1)
  have hslo : (0.3030651874:ℝ)^2 < planarC1^2 := by nlinarith only [he, hu, ht.1]
  have hshi : planarC1^2 < (0.3030651876:ℝ)^2 := by nlinarith only [he, hl, ht.2]
  constructor <;> nlinarith only [hslo, hshi, show 0 ≤ planarC1 from Real.sqrt_nonneg _]

 theorem planarFD_lt_decimal : planarFD < (0.595504:ℝ) := by
  rw [planarFD, div_lt_iff₀ Real.pi_pos]
  have hr : Real.sqrt (7/2:ℝ) < (1.87083:ℝ) := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 7/2), Real.sqrt_nonneg (7/2:ℝ)]
  nlinarith only [hr, Real.pi_gt_d6]

end
end ASDExplicitGamma.Triadic
