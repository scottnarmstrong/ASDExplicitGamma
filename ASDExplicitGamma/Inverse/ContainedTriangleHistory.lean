module

public import ASDExplicitGamma.Inverse.ContainedTriangleArea
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The raw source history pays for the complete contained-triangle dissection. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

/-- The source history weight written as an ordinary geometric power. -/
theorem history_weight_eq (r : ℕ) :
    (3 : ℝ) ^ (-(r : ℝ) / 2) = (1 / Real.sqrt 3) ^ r := by
  rw [show -(r : ℝ) / 2 = (-1 / 2 : ℝ) * r by ring,
    Real.rpow_mul_natCast (by norm_num), show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
    Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow, one_div]

/-- Each exact triangle depth weight is paid by the corresponding raw-history
weight with the sharp uniform factor 2 sqrt(3), for initial depth at most two. -/
theorem triangle_history_weight (a n : ℕ) (ha : a ≤ 2) :
    2 * (1 / 3 : ℝ) ^ (n + 1) ≤
      2 * Real.sqrt 3 * (3 : ℝ) ^ (-((a + n + 1 : ℕ) : ℝ) / 2) := by
  rw [history_weight_eq]
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have ht : 0 ≤ 1 / Real.sqrt 3 := by positivity
  have ht1 : 1 / Real.sqrt 3 ≤ 1 := by
    rw [div_le_iff₀ hs]
    nlinarith only [hsq, hs]
  have he : (1 / 3 : ℝ) = (1 / Real.sqrt 3) ^ 2 := by
    rw [div_pow, one_pow, hsq]
  rw [he, ← pow_mul, pow_succ (1 / Real.sqrt 3) (a + n)]
  have hc : 2 * Real.sqrt 3 * ((1 / Real.sqrt 3) ^ (a + n) * (1 / Real.sqrt 3)) =
      2 * (1 / Real.sqrt 3) ^ (a + n) := by field_simp
  rw [hc]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one ht ht1 (by omega : a + n ≤ 2 * (n + 1)))
    (by norm_num)

/-- Full countable triangle history comparison, using the raw sum rather than
an expectation of a square-root depth loss. -/
theorem triangle_raw_history_bound (M : ℕ → ℝ) (hM : ∀ r, 0 ≤ M r)
    (hS : Summable (fun r : ℕ => (3 : ℝ) ^ (-(r : ℝ) / 2) * M r))
    (a : ℕ) (ha : a ≤ 2) :
    (∑' n : ℕ, 2 * (1 / 3 : ℝ) ^ (n + 1) * M (a + n + 1)) ≤
      2 * Real.sqrt 3 * ∑' r : ℕ, (3 : ℝ) ^ (-(r : ℝ) / 2) * M r := by
  have hi : Function.Injective (fun n : ℕ => a + n + 1) := by
    intro n m h
    change a + n + 1 = a + m + 1 at h
    omega
  have hs := hS.comp_injective hi
  have hc := hs.mul_left (2 * Real.sqrt 3)
  have hle (n : ℕ) : 2 * (1 / 3 : ℝ) ^ (n + 1) * M (a + n + 1) ≤
      2 * Real.sqrt 3 * ((3 : ℝ) ^ (-((a + n + 1 : ℕ) : ℝ) / 2) * M (a + n + 1)) := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (triangle_history_weight a n ha)
      (hM (a + n + 1))
  have hh := hc.of_nonneg_of_le (fun n => mul_nonneg (by positivity) (hM _)) hle
  calc
    _ ≤ ∑' n : ℕ, 2 * Real.sqrt 3 *
        ((3 : ℝ) ^ (-((a + n + 1 : ℕ) : ℝ) / 2) * M (a + n + 1)) :=
      hh.tsum_le_tsum hle hc
    _ = 2 * Real.sqrt 3 * ∑' n : ℕ,
        (3 : ℝ) ^ (-((a + n + 1 : ℕ) : ℝ) / 2) * M (a + n + 1) := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (hs.tsum_le_tsum_of_inj (fun n : ℕ => a + n + 1) hi
        (fun r _ => mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hM r)) (fun _ => le_rfl) hS)
      (by positivity)

end ASDExplicitGamma.Inverse
