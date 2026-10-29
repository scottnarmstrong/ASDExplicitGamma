module

public import ASDExplicitGamma.Numerics.GeneratorEigenvalue

/-! The exact lower spectral constant for the main inverse generator. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open ASDExplicitGamma.Numerics

/-- The exact q3 shell amplitudes `A₂` and `A₄` in the MA source rows. -/
noncomputable def mainInverseA2 (v : ℝ) : ℝ := v / (3 : ℝ) ^ 12

noncomputable def mainInverseA4 (v : ℝ) : ℝ := v / (3 : ℝ) ^ 24

/-- The explicit first-channel coefficient in MA-TRACE-LOWER-GENERATOR. -/
noncomputable def mainInverseKA (v : ℝ) : ℝ :=
  Real.sqrt v + (1440 / 1000 : ℝ) *
      Real.sqrt ((156 / 5 : ℝ) * mainInverseA2 v) +
    (285 / 1000 : ℝ) * Real.sqrt ((46488 / 25 : ℝ) * mainInverseA4 v)

/-- The explicit reciprocal-channel coefficient in MA-TRACE-LOWER-GENERATOR. -/
noncomputable def mainInverseKB (v : ℝ) : ℝ :=
  Real.sqrt v + (1440 / 1000 : ℝ) *
      Real.sqrt ((78 / 5 : ℝ) * mainInverseA2 v) +
    (285 / 1000 : ℝ) * Real.sqrt ((23244 / 25 : ℝ) * mainInverseA4 v)

theorem mainInverseKA_nonneg (v : ℝ) : 0 ≤ mainInverseKA v := by
  unfold mainInverseKA mainInverseA2 mainInverseA4
  positivity

theorem mainInverseKB_nonneg (v : ℝ) : 0 ≤ mainInverseKB v := by
  unfold mainInverseKB mainInverseA2 mainInverseA4
  positivity

/-- The larger characteristic root bounds the quadratic form, including
zero coupling and the degenerate zero matrix. -/
theorem main_generator_quadratic_upper (a b : ℝ) (ha : 0 ≤ a) (u v : ℝ) :
    a * u ^ 2 + 2 * b * u * v ≤ generatorLambdaMax a b * (u ^ 2 + v ^ 2) := by
  let mu := generatorLambdaMax a b
  have hroot : mu ^ 2 - a * mu - b ^ 2 = 0 := generator_characteristic_root a b
  have hmu : 0 ≤ mu := by dsimp [mu, generatorLambdaMax]; positivity
  rcases hmu.eq_or_lt with hz | hp
  · have hm : mu = 0 := hz.symm
    have hb : b = 0 := by rw [hm] at hroot; nlinarith only [hroot, sq_nonneg b]
    have ha0 : a = 0 := by
      have hh : a + Real.sqrt (a ^ 2 + 4 * b ^ 2) = 0 := by
        simpa only [mu, generatorLambdaMax, div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false] using hm
      have hs := Real.sqrt_nonneg (a ^ 2 + 4 * b ^ 2)
      linarith only [ha, hh, hs]
    change a * u ^ 2 + 2 * b * u * v ≤ mu * (u ^ 2 + v ^ 2)
    simp only [ha0, hb, hm, zero_mul, mul_zero, zero_add, le_refl]
  · have heq : mu * (mu * (u ^ 2 + v ^ 2) - (a * u ^ 2 + 2 * b * u * v)) =
        (b * u - mu * v) ^ 2 := by
      calc
        _ = (mu ^ 2 - a * mu - b ^ 2) * u ^ 2 + (b * u - mu * v) ^ 2 := by ring
        _ = _ := by rw [hroot]; ring
    have hnonneg : 0 ≤ mu * (u ^ 2 + v ^ 2) - (a * u ^ 2 + 2 * b * u * v) := by
      apply (mul_nonneg_iff_of_pos_left hp).mp
      rw [heq]
      exact sq_nonneg _
    exact sub_nonneg.mp hnonneg

/-- The source inverse-system lower eigenvalue, with the half-gain constant
63/50. It is distinct from the forced-source spectral constant. -/
noncomputable def mainInverseMuMinus (ka kb : ℝ) : ℝ :=
  (kb ^ 2 + Real.sqrt (kb ^ 4 + 4 * (63 / 50 : ℝ) ^ 2 * ka ^ 2 * kb ^ 2)) / 2

/-- The source inverse-system lower eigenvalue with the two MA channel
coefficients fixed to their explicit q3 shell formulas. -/
noncomputable def mainInverseMuMinusSource (v : ℝ) : ℝ :=
  mainInverseMuMinus (mainInverseKA v) (mainInverseKB v)

/-- The literal source radicand agrees with the characteristic root. -/
theorem mainInverseMuMinus_eq (ka kb : ℝ) :
    mainInverseMuMinus ka kb = generatorLambdaMax (kb ^ 2) ((63 / 50 : ℝ) * ka * kb) := by
  unfold mainInverseMuMinus generatorLambdaMax
  congr 3
  ring

/-- The lower quadratic-form estimate used after the pathwise inverse
Hessian decomposition. No pathwise Hessian estimate is assumed here. -/
theorem main_inverse_lower_quadratic (ka kb u v : ℝ) :
    -(kb ^ 2 * u ^ 2 + 2 * (63 / 50 : ℝ) * ka * kb * u * v) ≥
      -(mainInverseMuMinus ka kb * (u ^ 2 + v ^ 2)) := by
  rw [mainInverseMuMinus_eq]
  apply neg_le_neg
  convert main_generator_quadratic_upper (kb ^ 2) ((63 / 50 : ℝ) * ka * kb)
    (sq_nonneg kb) u v using 1
  ring

end ASDExplicitGamma.Main
