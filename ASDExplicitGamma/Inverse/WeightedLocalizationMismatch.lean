module

public import ASDExplicitGamma.Inverse.WeightedLocalizationRadius

/-! The retained localization-mismatch coefficient, at every later effective depth. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

/-- Literal third PE coefficient, including both localization and expectation errors. -/
noncomputable def localizationMismatchCoefficient (m : ℕ) (p : ℝ) : ℝ :=
  2 * (80 * (m : ℝ) * p) ^ m * (12000 : ℝ) ^ (1 / (2 * p)) *
    Real.exp (-(3 : ℝ) ^ 11 / (6 * p)) * (3 : ℝ) ^ (130 : ℕ)

/-- The all-depth mismatch estimate has the exact retained rate nu_3=2.
Only the source order range p<=256 is used in its six-depth improvement. -/
theorem localization_retained_mismatch_bound (m : ℕ) (p : ℝ) (hp : 0 < p) (hp256 : p ≤ 256)
    (R : ℕ) (hR : 60 ≤ R) :
    2 * (80 * (m : ℝ) * p) ^ m * (12000 : ℝ) ^ (1 / (2 * p)) *
      Real.exp (-(localizationCutoffRadius R : ℝ) / (6 * p)) ≤
        localizationMismatchCoefficient m p * (3 : ℝ) ^ (-2 * (R : ℝ)) := by
  have hh := mul_le_mul_of_nonneg_left (localization_mismatch_exponential_decay p hp hp256 R hR)
    (show 0 ≤ 2 * (80 * (m : ℝ) * p) ^ m * (12000 : ℝ) ^ (1 / (2 * p)) by positivity)
  have he : (3 : ℝ) ^ (130 - 2 * (R : ℝ)) =
      (3 : ℝ) ^ (130 : ℕ) * (3 : ℝ) ^ (-2 * (R : ℝ)) := by
    rw [show (130 : ℝ) - 2 * (R : ℝ) = 130 + (-2 * (R : ℝ)) by ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    norm_num only [Real.rpow_ofNat]
  rw [he] at hh
  convert hh using 1
  unfold localizationMismatchCoefficient
  ring

end ASDExplicitGamma.Inverse
