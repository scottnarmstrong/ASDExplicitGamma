module

public import ASDExplicitGamma.Gaussian.GeneratorBounds

/-! Finite signed generator estimates from the actual source and feedback bounds. -/

@[expose] public section
namespace ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Numerics

/-- The sharp projected-source estimates imply the prescribed matrix
bound after retaining the favorable negative projection square. -/
theorem source_feedback_generator_le
    (ρ c B source cross negative x y E : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 243) (hB : 0 ≤ B)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hnegative : 0 ≤ negative)
    (hsource : source ≤ B * c ^ 2 * (generatorKA ρ) ^ 2 * x ^ 2)
    (hcross : cross ≤ (63 / 50 : ℝ) * B * c ^ 2 *
      generatorKA ρ * generatorKB ρ * x * y)
    (henergy : x ^ 2 + y ^ 2 ≤ B * E) :
    source + 2 * cross - negative ≤ 19 * c ^ 2 * B ^ 2 * E := by
  have hcaps := generator_coefficient_caps ρ hρ0 hρ
  have hH : (1 : ℝ) ≤ generatorH := by norm_num [generatorH]
  have hD : (63 / 50 : ℝ) ≤ generatorFeedback := by
    unfold generatorFeedback generatorH
    linarith only [Real.sqrt_nonneg (2.265 : ℝ)]
  have hA : (generatorKA ρ) ^ 2 * x ^ 2 ≤
      generatorH * (generatorKA ρ) ^ 2 * x ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hH
      (mul_nonneg (sq_nonneg (generatorKA ρ)) (sq_nonneg x))
    convert h using 1 <;> ring
  have hC : 2 * (63 / 50 : ℝ) * generatorKA ρ * generatorKB ρ * x * y ≤
      2 * generatorFeedback * generatorKA ρ * generatorKB ρ * x * y := by
    have hfactor : 0 ≤ 2 * generatorKA ρ * generatorKB ρ * x * y := by
      exact mul_nonneg (mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) hcaps.1.le) hcaps.2.2.1.le) hx) hy
    have h := mul_le_mul_of_nonneg_right hD hfactor
    convert h using 1 <;> ring
  have hquad : (generatorKA ρ) ^ 2 * x ^ 2 +
      2 * (63 / 50 : ℝ) * generatorKA ρ * generatorKB ρ * x * y ≤
      19 * (x ^ 2 + y ^ 2) :=
    (add_le_add hA hC).trans (generator_quadratic_le_19 ρ x y hρ0 hρ)
  have hBc : 0 ≤ B * c ^ 2 := mul_nonneg hB (sq_nonneg c)
  calc
    source + 2 * cross - negative ≤
        B * c ^ 2 * (generatorKA ρ) ^ 2 * x ^ 2 +
          2 * ((63 / 50 : ℝ) * B * c ^ 2 *
            generatorKA ρ * generatorKB ρ * x * y) := by
      linarith only [hsource, hcross, hnegative]
    _ = B * c ^ 2 * ((generatorKA ρ) ^ 2 * x ^ 2 +
        2 * (63 / 50 : ℝ) * generatorKA ρ * generatorKB ρ * x * y) := by ring
    _ ≤ B * c ^ 2 * (19 * (x ^ 2 + y ^ 2)) :=
      mul_le_mul_of_nonneg_left hquad hBc
    _ ≤ B * c ^ 2 * (19 * (B * E)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left henergy (by norm_num)) hBc
    _ = 19 * c ^ 2 * B ^ 2 * E := by ring

end ASDExplicitGamma.Gaussian
