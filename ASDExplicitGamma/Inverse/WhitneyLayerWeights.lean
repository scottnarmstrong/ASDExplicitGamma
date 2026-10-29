module

public import Mathlib.Analysis.SpecificLimits.Basic

/-! Exact planar Whitney layer fractions, retaining both geometric powers. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

/-- Source layer k+1: the central third-square first, then the finalized
boundary layers with their exact planar volume fractions. -/
noncomputable def bankLayerWeight (k : ℕ) : ℝ :=
  if k = 0 then 1 / 9 else 8 * (1 / 3 : ℝ) ^ (k + 1) - 32 * (1 / 9 : ℝ) ^ (k + 1)

@[simp] theorem layerWeight_zero : bankLayerWeight 0 = 1 / 9 := by
  simp only [bankLayerWeight, ite_true]

theorem layerWeight_succ (k : ℕ) :
    bankLayerWeight (k + 1) = 8 * (1 / 3 : ℝ) ^ (k + 2) - 32 * (1 / 9 : ℝ) ^ (k + 2) := by
  simp only [bankLayerWeight, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false]

theorem bankLayerWeight_nonneg (k : ℕ) : 0 ≤ bankLayerWeight k := by
  cases k with
  | zero => rw [layerWeight_zero]; norm_num
  | succ k =>
    rw [layerWeight_succ]
    have ha : 0 ≤ (1 / 3 : ℝ) ^ (k + 2) := by positivity
    have hb : (1 / 3 : ℝ) ^ (k + 2) ≤ 1 / 9 := by
      calc
        _ ≤ (1 / 3 : ℝ) ^ 2 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        _ = _ := by norm_num
    have he : (1 / 9 : ℝ) ^ (k + 2) = ((1 / 3 : ℝ) ^ (k + 2)) ^ 2 := by
      rw [← pow_mul, mul_comm (k + 2) 2, pow_mul]
      norm_num
    rw [he]
    nlinarith only [mul_nonneg ha (sub_nonneg.mpr hb)]

/-- The exact two-power source formula is summable and has total volume one. -/
theorem layerWeight_hasSum : HasSum bankLayerWeight 1 := by
  have ha := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 3)
    (by norm_num : (1 / 3 : ℝ) < 1)).mul_left (8 * (1 / 3 : ℝ) ^ 2)
  have hb := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 9)
    (by norm_num : (1 / 9 : ℝ) < 1)).mul_left (32 * (1 / 9 : ℝ) ^ 2)
  have ht : HasSum (fun k : ℕ => bankLayerWeight (k + 1)) (8 / 9) := by
    convert ha.sub hb using 1
    · funext k
      rw [layerWeight_succ, pow_add, pow_add]
      ring
    · norm_num
  have hh := ht.zero_add
  convert hh using 1
  norm_num [bankLayerWeight]

end ASDExplicitGamma.Inverse
