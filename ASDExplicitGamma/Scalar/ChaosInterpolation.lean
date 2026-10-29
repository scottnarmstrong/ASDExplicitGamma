module

public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! Weighted Hölder interpolation used by the corrected SC-CHAOS-MOMENT-BOUND.
The Gaussian second-chaos moment estimate is separate from this general helper. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory
open scoped ENNReal

/-- Interpolation between the first and second moments of an extended nonnegative observable. -/
theorem chaos_integral_interpolation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : Ω → ℝ≥0∞) (hY : AEMeasurable Y μ)
    (q : ℝ) (hq1 : 1 ≤ q) (hq2 : q ≤ 2) :
    (∫⁻ ω, (Y ω)^q ∂μ) ≤
      (∫⁻ ω, Y ω ∂μ)^(2-q)*(∫⁻ ω, (Y ω)^2 ∂μ)^(q-1) := by
  have h := ENNReal.lintegral_mul_norm_pow_le hY (hY.pow_const 2)
    (by linarith only [hq2] : 0 ≤ 2-q) (by linarith only [hq1] : 0 ≤ q-1)
    (by ring : (2-q)+(q-1)=1)
  convert h using 1
  apply lintegral_congr_ae
  filter_upwards with ω
  rw [← ENNReal.rpow_natCast,← ENNReal.rpow_mul]
  norm_num only [Nat.cast_ofNat]
  rw [← ENNReal.rpow_add_of_nonneg _ _ (by linarith only [hq2])
    (by nlinarith only [hq1] : 0 ≤ (2:ℝ)*(q-1))]
  congr 1
  ring

/-- The conjugate-exponent estimate after supplying a second-moment bound.
This helper does not assume or assert that an arbitrary Y is Gaussian chaos. -/
theorem chaos_conjugate_bound_of_second_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : Ω → ℝ≥0∞) (hY : Measurable Y)
    (C : ℝ≥0∞) (p : ℝ) (hp : 2 ≤ p)
    (hsecond : (∫⁻ ω, (Y ω)^2 ∂μ) ≤ C^2*(∫⁻ ω, Y ω ∂μ)^2) :
    eLpNorm Y (ENNReal.ofReal (p/(p-1))) μ ≤ C^(2/p)*(∫⁻ ω, Y ω ∂μ) := by
  let q := p/(p-1)
  have hp0 : 0 < p := by linarith only [hp]
  have hpm : 0 < p-1 := by linarith only [hp]
  have hq0 : 0 < q := div_pos hp0 hpm
  have hq1 : 1 ≤ q := by dsimp only [q]; apply (le_div_iff₀ hpm).mpr; linarith
  have hq2 : q ≤ 2 := by dsimp only [q]; apply (div_le_iff₀ hpm).mpr; linarith only [hp]
  have ha : 0 ≤ 2-q := by linarith only [hq2]
  have hb : 0 ≤ q-1 := by linarith only [hq1]
  have hqinv : 0 ≤ 1/q := (one_div_pos.mpr hq0).le
  have he : (2*(q-1))*(1/q) = 2/p := by dsimp only [q]; field_simp; ring
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top hY.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofReal (show 0 ≤ p/(p-1) from div_nonneg hp0.le hpm.le),enorm_eq_self]
  have h := chaos_integral_interpolation μ Y hY.aemeasurable q hq1 hq2
  have hs := ENNReal.rpow_le_rpow hsecond hb
  have ht := h.trans (mul_le_mul_of_nonneg_left hs (zero_le : (0:ℝ≥0∞) ≤ _))
  have hf := ENNReal.rpow_le_rpow ht hqinv
  rw [ENNReal.mul_rpow_of_nonneg _ _ hqinv,
    ENNReal.mul_rpow_of_nonneg _ _ hb,← ENNReal.rpow_natCast,
    ← ENNReal.rpow_mul,← ENNReal.rpow_mul] at hf
  simp only [ENNReal.mul_rpow_of_nonneg _ _ hqinv,← ENNReal.rpow_natCast,← ENNReal.rpow_mul,Nat.cast_ofNat] at hf
  have hm : (2-q)*(1/q)+(2*(q-1))*(1/q) = 1 := by field_simp; ring
  have hr : (∫⁻ ω, Y ω ∂μ)^((2-q)*(1/q))*
      (∫⁻ ω, Y ω ∂μ)^((2*(q-1))*(1/q)) = ∫⁻ ω, Y ω ∂μ := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (mul_nonneg ha hqinv)
      (mul_nonneg (mul_nonneg (by norm_num) hb) hqinv),hm,ENNReal.rpow_one]
  calc
    _ ≤ _ := hf
    _ = C^(2/p)*(∫⁻ ω, Y ω ∂μ) := by
      rw [← mul_assoc,mul_comm ((∫⁻ ω, Y ω ∂μ)^((2-q)*(1/q))),mul_assoc,hr,he]

end ASDExplicitGamma.Scalar
