module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The joint-disk maximum and paired-potential cross bound in the OLD trial. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory

/-- The disk radius used by the source joint-disk estimate. -/
noncomputable def lambda3Alpha : ℝ := (3 : ℝ) ^ (-(1 / 4 : ℝ))

/-- The joint-disk output factor, with the source value of alpha. -/
noncomputable def lambda3PureFactor : ℝ :=
  Real.sqrt (lambda3Alpha ^ 2 + 1 / 2 + Real.sqrt (1 / 4 + lambda3Alpha ^ 2))

/-- The one-pure-leg cross constant from the source audit. -/
noncomputable def lambda3Dx : ℝ := 141 / 100

/-- The scalar joint-disk maximum: on the unit disk, the linear functional
x/2 + q y is bounded by its Euclidean coefficient norm. -/
theorem lambda3_joint_disk_residue (t q : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t + q ^ 2 + 2 * q * Real.sqrt (t - t ^ 2) ≤
      q ^ 2 + 1 / 2 + Real.sqrt (1 / 4 + q ^ 2) := by
  let x := 2 * t - 1
  let y := 2 * Real.sqrt (t - t ^ 2)
  have hrad : 0 ≤ t - t ^ 2 := by
    have h := mul_nonneg ht0 (sub_nonneg.mpr ht1)
    nlinarith only [h]
  have hunit : x ^ 2 + y ^ 2 = 1 := by
    dsimp [x, y]
    rw [mul_pow, Real.sq_sqrt hrad]
    ring
  have hcs : (x / 2 + q * y) ^ 2 ≤ (1 / 4 + q ^ 2) * (x ^ 2 + y ^ 2) := by
    nlinarith only [sq_nonneg (q * x - y / 2)]
  have hcs' : (x / 2 + q * y) ^ 2 ≤ 1 / 4 + q ^ 2 := by
    rw [hunit] at hcs
    nlinarith only [hcs]
  have hroot_nonneg : 0 ≤ Real.sqrt (1 / 4 + q ^ 2) := Real.sqrt_nonneg _
  have hroot_sq : Real.sqrt (1 / 4 + q ^ 2) ^ 2 = 1 / 4 + q ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hlin : x / 2 + q * y ≤ Real.sqrt (1 / 4 + q ^ 2) := by
    by_cases hxy : x / 2 + q * y ≤ 0
    · exact hxy.trans hroot_nonneg
    · have hxypos : 0 < x / 2 + q * y := lt_of_not_ge hxy
      have hsq : (x / 2 + q * y) ^ 2 ≤ Real.sqrt (1 / 4 + q ^ 2) ^ 2 := by
        nlinarith only [hcs', hroot_sq]
      exact (sq_le_sq₀ (le_of_lt hxypos) hroot_nonneg).mp hsq
  calc
    t + q ^ 2 + 2 * q * Real.sqrt (t - t ^ 2) =
        q ^ 2 + (1 / 2 + (x / 2 + q * y)) := by
      dsimp [x, y]
      ring
    _ = (q ^ 2 + 1 / 2) + (x / 2 + q * y) := by ring
    _ ≤ (q ^ 2 + 1 / 2) + Real.sqrt (1 / 4 + q ^ 2) := by
      calc
        _ = (x / 2 + q * y) + (q ^ 2 + 1 / 2) := by ring
        _ ≤ Real.sqrt (1 / 4 + q ^ 2) + (q ^ 2 + 1 / 2) :=
          add_le_add_left hlin _
        _ = _ := by ring
    _ = q ^ 2 + 1 / 2 + Real.sqrt (1 / 4 + q ^ 2) := by ring

/-- The source pure factor is strictly below its outward 1.410 cross
coefficient. -/
theorem lambda3_pure_factor_lt_Dx : lambda3PureFactor < lambda3Dx := by
  have hAlphaSq : lambda3Alpha ^ 2 = (Real.sqrt 3)⁻¹ := by
    unfold lambda3Alpha
    rw [← Real.rpow_two, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
      show (-(1 / 4 : ℝ)) * 2 = -(1 / 2 : ℝ) by norm_num,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), ← Real.sqrt_eq_rpow 3]
  have hrootLower : (1732 / 1000 : ℝ) ≤ Real.sqrt 3 := by
    have hsquare : (1732 / 1000 : ℝ) ^ 2 ≤ (Real.sqrt 3) ^ 2 := by
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num
    nlinarith [Real.sqrt_nonneg (3 : ℝ), hsquare]
  have hrootPos : 0 < Real.sqrt 3 := by positivity
  have hAlphaSqLe : lambda3Alpha ^ 2 ≤ 578 / 1000 := by
    rw [hAlphaSq]
    rw [inv_le_iff_one_le_mul₀' hrootPos]
    nlinarith only [hrootLower]
  have hinnerRoot : Real.sqrt (1 / 4 + lambda3Alpha ^ 2) ≤ 91 / 100 := by
    rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 91 / 100)]
    nlinarith only [hAlphaSqLe]
  have hrad : lambda3Alpha ^ 2 + 1 / 2 +
      Real.sqrt (1 / 4 + lambda3Alpha ^ 2) < (141 / 100 : ℝ) ^ 2 := by
    nlinarith only [hAlphaSqLe, hinnerRoot]
  unfold lambda3PureFactor lambda3Dx
  exact (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 141 / 100)).2 hrad

end ASDExplicitGamma.Scalar
