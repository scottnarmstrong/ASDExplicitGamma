module

public import ASDExplicitGamma.Gaussian.SpatialKernelSupport

/-! # Local L² mass controls each physical q3 convolution value -/

@[expose] public section

open MeasureTheory Homogenization Set
open scoped RealInnerProductSpace

namespace ASDExplicitGamma.Gaussian

/-- White-noise input restricted to the precise kernel support box. -/
noncomputable def whiteNoiseInBox (L : {l : ℝ // 0 < l}) (x : Vec 2) (u : WhiteNoise) : WhiteNoise :=
  ((Lp.memLp u).indicator (measurableSet_q3SupportBox L x)).toLp ((q3SupportBox L x).indicator u)

theorem whiteNoiseInBox_ae (L : {l : ℝ // 0 < l}) (x : Vec 2) (u : WhiteNoise) :
    whiteNoiseInBox L x u =ᵐ[volume] (q3SupportBox L x).indicator u :=
  ((Lp.memLp u).indicator (measurableSet_q3SupportBox L x)).coeFn_toLp

/-- The restricted Hilbert norm is the ordinary local input L² mass. -/
theorem whiteNoiseInBox_norm_sq (L : {l : ℝ // 0 < l}) (x : Vec 2) (u : WhiteNoise) :
    ‖whiteNoiseInBox L x u‖ ^ 2 = ∫ y in q3SupportBox L x, u y ^ 2 := by
  rw [l2_norm_sq]
  calc
    _ = ∫ y, (q3SupportBox L x).indicator (fun y => u y ^ 2) y := by
      apply integral_congr_ae
      filter_upwards [whiteNoiseInBox_ae L x u] with y hy
      rw [hy]
      by_cases hmem : y ∈ q3SupportBox L x
      · simp only [indicator_of_mem hmem, Real.norm_eq_abs, sq_abs]
      · simp only [indicator_of_notMem hmem, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
    _ = _ := integral_indicator (measurableSet_q3SupportBox L x)

/-- Localizing the input does not change its pairing with the physical kernel section. -/
theorem inner_whiteNoiseInBox_section (β : ℝ) (L : {l : ℝ // 0 < l}) (x : Vec 2) (u : WhiteNoise) :
    ⟪whiteNoiseInBox L x u, q3Section β L h3Zero x⟫ = ⟪u, q3Section β L h3Zero x⟫ := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [whiteNoiseInBox_ae L x u, (q3SectionFunction_memLp β L h3Zero x).coeFn_toLp] with y hu hk
  change q3Section β L h3Zero x y = q3SectionFunction β L h3Zero x y at hk
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, hu, hk]
  by_cases hy : y ∈ q3SupportBox L x
  · rw [indicator_of_mem hy]
  · rw [indicator_of_notMem hy, q3SectionFunction_zero_outside β L x y hy, mul_zero, zero_mul]

/-- The support-localized Cauchy–Schwarz estimate; integrating the moving box gives the
L²→L⁴ improvement for fine shells. -/
theorem q3Convolution_sq_le_local_mass (β : ℝ) (L : {l : ℝ // 0 < l}) (u : WhiteNoise) (x : Vec 2) :
    q3Convolution β L h3Zero u x ^ 2 ≤ β ^ 2 * ∫ y in q3SupportBox L x, u y ^ 2 := by
  have hh := pow_le_pow_left₀ (norm_nonneg _)
    (norm_inner_le_norm (𝕜 := ℝ) (whiteNoiseInBox L x u) (q3Section β L h3Zero x)) 2
  rw [Real.norm_eq_abs, sq_abs, mul_pow, q3Section_norm_sq, whiteNoiseInBox_norm_sq,
    inner_whiteNoiseInBox_section] at hh
  exact hh.trans_eq (mul_comm _ _)

/-- The other operator bound is the global point-evaluation Cauchy–Schwarz estimate. -/
theorem q3Convolution_sq_le_global_mass (β : ℝ) (L : {l : ℝ // 0 < l}) (u : WhiteNoise) (x : Vec 2) :
    q3Convolution β L h3Zero u x ^ 2 ≤ β ^ 2 * ‖u‖ ^ 2 := by
  have hh := pow_le_pow_left₀ (norm_nonneg _)
    (norm_inner_le_norm (𝕜 := ℝ) u (q3Section β L h3Zero x)) 2
  rw [Real.norm_eq_abs, sq_abs, mul_pow, q3Section_norm_sq] at hh
  exact hh.trans_eq (mul_comm _ _)

end ASDExplicitGamma.Gaussian
