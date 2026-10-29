module

public import ASDExplicitGamma.Inverse.WeightedLocalizationMismatch
public import ASDExplicitGamma.Numerics.Inverse.Localization64
public import ASDExplicitGamma.Numerics.Inverse.Localization128

/-! Actual localization-mismatch coefficients consume the literal Taylor certificates. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

/-- The source root of 12000 is at most two throughout the consumed moment range. -/
theorem localization_mismatch_root_le_two (p : ℝ) (hp : 7 ≤ p) :
    (12000 : ℝ) ^ (1 / (2 * p)) ≤ 2 := by
  rw [one_div, Real.rpow_inv_le_iff_of_pos (by norm_num) (by norm_num) (by linarith : 0 < 2 * p)]
  calc
    (12000 : ℝ) ≤ (2 : ℝ) ^ (14 : ℝ) := by norm_num
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hp])

/-- The exact scalar mismatch coefficient is bounded by its 513-term Taylor
certificate. No exponential remainder estimate or decimal approximation is assumed. -/
theorem localization_mismatch_taylor_bound (p : ℝ) (hp : 7 ≤ p) :
    localizationMismatchCoefficient 4 p ≤
      4 * (320 * p) ^ (4 : ℕ) * (3 : ℝ) ^ (130 : ℕ) /
        (∑ i ∈ Finset.range 513, ((3 : ℝ) ^ (11 : ℕ) / (6 * p)) ^ i / (Nat.factorial i : ℝ)) := by
  let A := (3 : ℝ) ^ (11 : ℕ) / (6 * p)
  let S := ∑ i ∈ Finset.range 513, A ^ i / (Nat.factorial i : ℝ)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hS : 1 ≤ S := by
    have hh := Finset.single_le_sum (s := Finset.range 513)
      (f := fun i => A ^ i / (Nat.factorial i : ℝ)) (fun i _ => by positivity)
      (show 0 ∈ Finset.range 513 by simp)
    simpa only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] using hh
  have he : S ≤ Real.exp A := Real.sum_le_exp_of_nonneg hA 513
  have hinv : Real.exp (-A) ≤ 1 / S := by
    calc
      Real.exp (-A) = 1 / Real.exp A := by
        rw [Real.exp_neg]
        exact (one_div (Real.exp A)).symm
      _ ≤ _ := one_div_le_one_div_of_le (by linarith only [hS] : 0 < S) he
  have hprod := mul_le_mul (localization_mismatch_root_le_two p hp) hinv
    (Real.exp_pos (-A)).le (by norm_num : (0 : ℝ) ≤ 2)
  have hh := mul_le_mul_of_nonneg_left hprod
    (show 0 ≤ 2 * (320 * p) ^ (4 : ℕ) * (3 : ℝ) ^ (130 : ℕ) by positivity)
  have hbase : 80 * (4 : ℝ) * p = 320 * p := by ring
  have hexp : -(3 : ℝ) ^ (11 : ℕ) / (6 * p) = -A := by dsimp only [A]; ring
  unfold localizationMismatchCoefficient
  simp only [Nat.cast_ofNat]
  rw [hbase, hexp]
  change _ ≤ 4 * (320 * p) ^ (4 : ℕ) * (3 : ℝ) ^ (130 : ℕ) / S
  calc
    _ = 2 * (320 * p) ^ (4 : ℕ) * (3 : ℝ) ^ (130 : ℕ) *
        ((12000 : ℝ) ^ (1 / (2 * p)) * Real.exp (-A)) := by ring
    _ ≤ _ := hh
    _ = _ := by ring

/-- At the full-response order 64 the actual source mismatch coefficient fits
inside the literal rational certificate. -/
theorem localization_mismatch64_le_numeric :
    localizationMismatchCoefficient 4 64 ≤ (Numerics.Inverse.invLocalization64 : ℝ) := by
  have hh := localization_mismatch_taylor_bound 64 (by norm_num)
  convert hh using 1
  unfold Numerics.Inverse.invLocalization64
  push_cast
  rfl

/-- The same physical coefficient is certified separately at order 128. -/
theorem localization_mismatch128_le_numeric :
    localizationMismatchCoefficient 4 128 ≤ (Numerics.Inverse.invLocalization128 : ℝ) := by
  have hh := localization_mismatch_taylor_bound 128 (by norm_num)
  convert hh using 1
  unfold Numerics.Inverse.invLocalization128
  push_cast
  rfl

/-- The corrected localization-offset payments apply to the actual physical
coefficients at both consumed full-response orders. -/
theorem localization_mismatch_offset_payments :
    (13 : ℝ) ^ 2 * localizationMismatchCoefficient 4 64 < 9 ^ 2 ∧
      (13 : ℝ) ^ 2 * localizationMismatchCoefficient 4 128 < 9 ^ 2 := by
  have h64 : (13 : ℝ) ^ 2 * (Numerics.Inverse.invLocalization64 : ℝ) < 9 ^ 2 := by
    exact_mod_cast Numerics.Inverse.invLocalization64_payment
  have h128 : (13 : ℝ) ^ 2 * (Numerics.Inverse.invLocalization128 : ℝ) < 9 ^ 2 := by
    exact_mod_cast Numerics.Inverse.invLocalization128_payment
  exact ⟨(mul_le_mul_of_nonneg_left localization_mismatch64_le_numeric (by norm_num)).trans_lt h64,
    (mul_le_mul_of_nonneg_left localization_mismatch128_le_numeric (by norm_num)).trans_lt h128⟩

end ASDExplicitGamma.Inverse
