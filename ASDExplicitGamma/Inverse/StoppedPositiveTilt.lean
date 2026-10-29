module

public import ASDExplicitGamma.Inverse.StoppedLabelWeights

/-! Literal positive-label side lengths and source exponential tilt coefficient. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
noncomputable section

/-- The aligned activation cube for positive label n+1 has side 3^(n+1). -/
def positiveLabelSide (n : ℕ) : ℝ := 3^(n+1)

theorem positive_label_side_pos (n : ℕ) : 0 < positiveLabelSide n := by
  unfold positiveLabelSide
  positivity

/-- The square-root side cancels the geometric label mass exactly. -/
theorem positive_sqrt_side_weight (n : ℕ) :
    Real.sqrt (positiveLabelSide n)*positiveLabelWeight n = (Real.sqrt 3-1)/2 := by
  unfold positiveLabelSide positiveLabelWeight labelWeightRatio
  have hroot : Real.sqrt ((3:ℝ)^(n+1)) = (Real.sqrt 3)^(n+1) := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) _)).mp
    rw [Real.sq_sqrt (by positivity), ← pow_mul, Nat.mul_comm (n+1) 2,
      pow_mul, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  rw [hroot,pow_succ,inv_pow]
  have hS : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 3)).ne'
  have hP : (Real.sqrt 3)^n ≠ 0 := pow_ne_zero n hS
  field_simp [hS,hP]

/-- The exact source coefficient 90/(sqrt(3)-1) is at most 123. -/
theorem positive_tilt_coefficient : (45:ℝ) ≤ 123*((Real.sqrt 3-1)/2) := by
  have hs : (71/41:ℝ) ≤ Real.sqrt 3 := (Real.le_sqrt (by norm_num : (0:ℝ) ≤ 71/41) (by norm_num : (0:ℝ) ≤ 3)).mpr (by norm_num)
  linarith only [hs]

/-- Nine residue colors retain the source tilt coefficient at every label. -/
theorem positive_label_tilt_le (n : ℕ) :
    5*positiveLabelSide n/(positiveLabelWeight n/9) ≤
      123*positiveLabelSide n*Real.sqrt (positiveLabelSide n) := by
  apply (div_le_iff₀ (div_pos (positive_label_weight_pos n) (by norm_num))).mpr
  calc
    _ ≤ positiveLabelSide n*(123*((Real.sqrt 3-1)/2))/9 := by
      have hh := mul_le_mul_of_nonneg_left positive_tilt_coefficient (positive_label_side_pos n).le
      nlinarith only [hh]
    _ = _ := by
      rw [← positive_sqrt_side_weight n]
      ring

end
end ASDExplicitGamma.Inverse
