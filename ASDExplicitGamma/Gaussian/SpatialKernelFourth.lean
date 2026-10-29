module

public import ASDExplicitGamma.Gaussian.SpatialKernelLocalization
public import ASDExplicitGamma.Gaussian.SpatialMovingBox

/-! # The physical q3 factor's sharp spatial L²→L⁴ scale gain -/

@[expose] public section

open MeasureTheory Homogenization

namespace ASDExplicitGamma.Gaussian

section
variable (β : ℝ) (L : {l : ℝ // 0 < l}) (u : WhiteNoise)
  (μ : Measure (Vec 2)) [IsFiniteMeasure μ]

/-- Physical convolutions have finite spatial second moments on every finite measure. -/
theorem integrable_q3Convolution_sq :
    Integrable (fun x => q3Convolution β L h3Zero u x ^ 2) μ := by
  apply Integrable.of_bound ((q3Convolution_continuous β L h3Zero u).pow 2).aestronglyMeasurable
    (β ^ 2 * ‖u‖ ^ 2)
  exact ae_of_all μ fun x => by
    simp only [Pi.pow_apply]
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact q3Convolution_sq_le_global_mass β L u x

/-- The same statement at the fourth moment is uniform before a spatial restriction. -/
theorem integrable_q3Convolution_pow_four :
    Integrable (fun x => q3Convolution β L h3Zero u x ^ 4) μ := by
  apply Integrable.of_bound ((q3Convolution_continuous β L h3Zero u).pow 4).aestronglyMeasurable
    ((β ^ 2 * ‖u‖ ^ 2) ^ 2)
  exact ae_of_all μ fun x => by
    simp only [Pi.pow_apply]
    rw [Real.norm_of_nonneg (by positivity : 0 ≤ q3Convolution β L h3Zero u x ^ 4)]
    have hh := pow_le_pow_left₀ (sq_nonneg _) (q3Convolution_sq_le_global_mass β L u x) 2
    simpa only [← pow_mul] using hh

/-- Fine shells gain the physical area L² in the fourth-power integral. This proves the
source Young-convolution estimate without requiring a general Young Lp theorem. -/
theorem integral_q3Convolution_pow_four_le_fine (hμ : μ ≤ volume) :
    (∫ x, q3Convolution β L h3Zero u x ^ 4 ∂μ) ≤ β ^ 4 * L.1 ^ 2 * ‖u‖ ^ 4 := by
  let C := β ^ 2 * ‖u‖ ^ 2
  have hC : 0 ≤ C := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hf := integrable_q3Convolution_sq β L u μ
  have h4 := integrable_q3Convolution_pow_four β L u μ
  have hmass := integrable_moving_q3SupportBox L μ u
  have hsq : (∫ x, q3Convolution β L h3Zero u x ^ 2 ∂μ) ≤
      β ^ 2 * ∫ x, ∫ y in q3SupportBox L x, u y ^ 2 ∂volume ∂μ := by
    rw [← integral_const_mul]
    exact integral_mono hf (hmass.const_mul _) (q3Convolution_sq_le_local_mass β L u)
  calc
    _ ≤ ∫ x, C * q3Convolution β L h3Zero u x ^ 2 ∂μ := by
      apply integral_mono h4 (hf.const_mul C)
      intro x
      have hh := mul_le_mul_of_nonneg_right (q3Convolution_sq_le_global_mass β L u x)
        (sq_nonneg (q3Convolution β L h3Zero u x))
      convert hh using 1
      ring
    _ = C * ∫ x, q3Convolution β L h3Zero u x ^ 2 ∂μ := integral_const_mul C _
    _ ≤ C * (β ^ 2 * ∫ x, ∫ y in q3SupportBox L x, u y ^ 2 ∂volume ∂μ) := mul_le_mul_of_nonneg_left hsq hC
    _ ≤ C * (β ^ 2 * (L.1 ^ 2 * ‖u‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (integral_moving_q3SupportBox_le L μ hμ u) (sq_nonneg β)) hC
    _ = _ := by dsimp only [C]; ring

/-- The companion coarse-shell estimate uses the finite spatial volume. -/
theorem integral_q3Convolution_pow_four_le_coarse :
    (∫ x, q3Convolution β L h3Zero u x ^ 4 ∂μ) ≤ β ^ 4 * μ.real Set.univ * ‖u‖ ^ 4 := by
  have hh := integral_mono (integrable_q3Convolution_pow_four β L u μ)
    (integrable_const ((β ^ 2 * ‖u‖ ^ 2) ^ 2)) (fun x => by
      have h := pow_le_pow_left₀ (sq_nonneg _) (q3Convolution_sq_le_global_mass β L u x) 2
      simpa only [← pow_mul] using h)
  rw [integral_const, smul_eq_mul] at hh
  exact hh.trans_eq (by ring)

end
end ASDExplicitGamma.Gaussian
