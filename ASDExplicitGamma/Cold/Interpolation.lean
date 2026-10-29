module

public import ASDExplicitGamma.Cold.ExactCentering
public import ASDExplicitGamma.Numerics.Cold.Basic
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! # The cold L¹/L²⁰ interpolation step -/

@[expose] public section

namespace ASDExplicitGamma.Cold

open MeasureTheory
open scoped ENNReal NNReal

/-- The precise L¹/L²⁰ interpolation exponents used by the cold recurrence. -/
theorem eLpNorm_two_le_one_twenty {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {X : Ω → ℝ} (hX : AEStronglyMeasurable X μ) :
    eLpNorm X 2 μ ≤ (eLpNorm X 1 μ) ^ (9 / 19 : ℝ) *
      (eLpNorm X 20 μ) ^ (10 / 19 : ℝ) := by
  have h := ENNReal.lintegral_mul_norm_pow_le
    (f := fun omega => ‖X omega‖ₑ) (g := fun omega => ‖X omega‖ₑ ^ (20 : ℝ))
    hX.enorm (hX.enorm.pow_const 20)
    (by norm_num : (0 : ℝ) ≤ 18 / 19) (by norm_num : (0 : ℝ) ≤ 1 / 19)
    (by norm_num : (18 / 19 : ℝ) + 1 / 19 = 1)
  have hfun : (fun omega => ‖X omega‖ₑ ^ (18 / 19 : ℝ) *
      (‖X omega‖ₑ ^ (20 : ℝ)) ^ (1 / 19 : ℝ)) =
      fun omega => ‖X omega‖ₑ ^ (2 : ℝ) := by
    funext omega
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  rw [hfun] at h
  have hroot := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hX]
  norm_num only [ENNReal.toReal_ofNat] at *
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul] at hroot
  have h1 : (eLpNorm X 1 μ) ^ (1 : ℝ) = ∫⁻ omega, ‖X omega‖ₑ ^ (1 : ℝ) ∂μ :=
    eLpNorm_nnreal_pow_eq_lintegral (p := (1 : ℝ≥0)) (by norm_num) hX
  have h20 : (eLpNorm X 20 μ) ^ (20 : ℝ) = ∫⁻ omega, ‖X omega‖ₑ ^ (20 : ℝ) ∂μ :=
    eLpNorm_nnreal_pow_eq_lintegral (p := (20 : ℝ≥0)) (by norm_num) hX
  simp only [ENNReal.rpow_one] at h1
  rw [← h1, ← h20, ← ENNReal.rpow_mul] at hroot
  norm_num at hroot ⊢
  exact hroot

/-- Real-valued interpolation for a finite L²⁰ random variable. -/
theorem lpNorm_two_le_one_twenty {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : MemLp X 20 μ) :
    lpNorm X 2 μ ≤ (lpNorm X 1 μ) ^ (9 / 19 : ℝ) *
      (lpNorm X 20 μ) ^ (10 / 19 : ℝ) := by
  have h1 := hX.mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 20)
  have h := eLpNorm_two_le_one_twenty μ hX.aestronglyMeasurable
  have hfin : (eLpNorm X 1 μ) ^ (9 / 19 : ℝ) *
      (eLpNorm X 20 μ) ^ (10 / 19 : ℝ) ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) h1.eLpNorm_ne_top)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hX.eLpNorm_ne_top)
  have hr := ENNReal.toReal_mono hfin h
  simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, toReal_eLpNorm] using hr

/-- CO-COLD-LAG-INTERPOLATION: source L¹ and L²⁰ caps control the centered
L² norm with exponents 9/19 and 10/19. No centered L¹ estimate is assumed. -/
theorem centered_l2_le_interpolated_caps {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ} {D M : ℝ}
    (hX : MemLp X 20 μ) (hnonneg : ∀ᵐ omega ∂μ, 0 ≤ X omega)
    (hmean : (∫ omega, X omega ∂μ) ≤ D) (hmoment : lpNorm X 20 μ ≤ M) :
    lpNorm (fun omega => X omega - ∫ a, X a ∂μ) 2 μ ≤
      D ^ (9 / 19 : ℝ) * M ^ (10 / 19 : ℝ) := by
  have h1 : lpNorm X 1 μ ≤ D := by
    rw [lpNorm_one_eq_integral_norm hX.aestronglyMeasurable]
    have heq : (∫ omega, ‖X omega‖ ∂μ) = ∫ omega, X omega ∂μ :=
      integral_congr_ae (hnonneg.mono fun omega hx => by
        change ‖X omega‖ = X omega
        exact Real.norm_of_nonneg hx)
    rwa [heq]
  have h2 := hX.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 20)
  have hcenter := lpNorm_sub_mean_le μ (by norm_num : (2 : ℝ) ≤ 2)
    (show MemLp X (ENNReal.ofReal 2) μ by simpa using h2) hnonneg
  calc
    _ ≤ lpNorm X 2 μ := by simpa only [ENNReal.ofReal_ofNat] using hcenter
    _ ≤ (lpNorm X 1 μ) ^ (9 / 19 : ℝ) * (lpNorm X 20 μ) ^ (10 / 19 : ℝ) :=
      lpNorm_two_le_one_twenty μ hX
    _ ≤ _ := mul_le_mul
      (Real.rpow_le_rpow lpNorm_nonneg h1 (by norm_num))
      (Real.rpow_le_rpow lpNorm_nonneg hmoment (by norm_num))
      (Real.rpow_nonneg lpNorm_nonneg _) (Real.rpow_nonneg (lpNorm_nonneg.trans h1) _)

/-- A power certificate bounds the endpoint interpolation radical. -/
theorem interpolation_radical_le_of_power {a R L : ℝ}
    (ha : 0 ≤ a) (hR : 0 ≤ R) (hL : 0 ≤ L)
    (hpower : a ^ 9 * R ^ 10 ≤ L ^ 19) :
    a ^ (9 / 19 : ℝ) * R ^ (10 / 19 : ℝ) ≤ L := by
  apply (pow_le_pow_iff_left₀
    (mul_nonneg (Real.rpow_nonneg ha _) (Real.rpow_nonneg hR _)) hL
    (by norm_num : (19 : ℕ) ≠ 0)).mp
  have haPow : (a ^ (9 / 19 : ℝ)) ^ (19 : ℕ) = a ^ (9 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
    norm_num
  have hRPow : (R ^ (10 / 19 : ℝ)) ^ (19 : ℕ) = R ^ (10 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR]
    norm_num
  rwa [mul_pow, haPow, hRPow]

/-- The NU-CO-ROOT2 exact certificate gives the stated cold L² endpoint. -/
theorem cold_endpoint_interpolation_le :
    (3 / 50 : ℝ) ^ (9 / 19 : ℝ) *
      (2013 / 10000 : ℝ) ^ (10 / 19 : ℝ) ≤ 5673 / 50000 := by
  apply interpolation_radical_le_of_power (by norm_num) (by norm_num) (by norm_num)
  have h : ((Numerics.Cold.coldA ^ 9 * Numerics.Cold.coldR20 ^ 10 : ℚ) : ℝ) ≤
      ((Numerics.Cold.coldL0 ^ 19 : ℚ) : ℝ) :=
    Rat.cast_le.mpr Numerics.Cold.coldRoot2
  simpa only [Numerics.Cold.coldA, Numerics.Cold.coldR20, Numerics.Cold.coldL0,
    Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat] using h

/-- The complete source minimum of the endpoint and updated lag interpolants.
The two pairs of inputs are the source global and lag-specific moment caps. -/
theorem centered_l2_le_cold_lag_cap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ} {D M : ℝ}
    (hX : MemLp X 20 μ) (hnonneg : ∀ᵐ omega ∂μ, 0 ≤ X omega)
    (hmean : (∫ omega, X omega ∂μ) ≤ D) (hmoment : lpNorm X 20 μ ≤ M)
    (hmeanGlobal : (∫ omega, X omega ∂μ) ≤ 3 / 50)
    (hmomentGlobal : lpNorm X 20 μ ≤ 2013 / 10000) :
    lpNorm (fun omega => X omega - ∫ a, X a ∂μ) 2 μ ≤
      min (5673 / 50000) (D ^ (9 / 19 : ℝ) * M ^ (10 / 19 : ℝ)) := by
  exact le_min
    ((centered_l2_le_interpolated_caps μ hX hnonneg hmeanGlobal hmomentGlobal).trans
      cold_endpoint_interpolation_le)
    (centered_l2_le_interpolated_caps μ hX hnonneg hmean hmoment)

end ASDExplicitGamma.Cold
