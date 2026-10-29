module

public import ASDExplicitGamma.Gaussian.GaussMomentHolder
public import ASDExplicitGamma.Gaussian.RioScalar
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-! # The exact Hölder estimate in the Lp squared-norm second variation -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ASDExplicitGamma.Gaussian

/-- Real scalar moment with the ordinary measure normalization. -/
noncomputable def rioMoment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : ℝ) (f : Ω → ℝ) : ℝ := ∫ ω, |f ω| ^ p ∂μ

/-- The squared finite Lp seminorm is the 2/p power of this moment. -/
theorem rio_lpNorm_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {p : ℝ} (hp : 0 < p) {f : Ω → ℝ} (hf : MemLp f (ENNReal.ofReal p) μ) :
    (eLpNorm f (ENNReal.ofReal p) μ).toReal ^ 2 = rioMoment μ p f ^ (2 / p) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by positivity) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by positivity)]
  simp only [ENNReal.toReal_ofReal hp.le, Real.norm_eq_abs]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (integral_nonneg fun _ => by positivity)]
  congr 1
  simp only [Nat.cast_ofNat]
  ring

/-- The second-variation integrand is integrable for every finite p ≥ 2. -/
theorem rio_integrable_second_product {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {p : ℝ} (hp : 2 < p) {Y X : Ω → ℝ}
    (hY : MemLp Y (ENNReal.ofReal p) μ) (hX : MemLp X (ENNReal.ofReal p) μ) :
    Integrable (fun ω => |Y ω| ^ (p - 2) * X ω ^ 2) μ := by
  have hq : 0 < p - 2 := by linarith only [hp]
  have hy := hY.norm_rpow_div (ENNReal.ofReal (p - 2))
  have hx := hX.norm_rpow_div (ENNReal.ofReal 2)
  rw [← ENNReal.ofReal_div_of_pos hq] at hy
  rw [← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)] at hx
  simp only [ENNReal.toReal_ofReal hq.le, Real.norm_eq_abs] at hy
  simp only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2), Real.norm_eq_abs,
    Real.rpow_two, sq_abs] at hx
  have hconj : (p / (p - 2)).HolderConjugate (p / 2) := by
    apply Real.holderConjugate_iff.mpr
    constructor
    · exact (one_lt_div hq).mpr (by linarith only [hp])
    · field_simp
      ring
  let holder : ENNReal.HolderTriple (ENNReal.ofReal (p / (p - 2))) (ENNReal.ofReal (p / 2)) 1 :=
    hconj.ennrealOfReal
  exact hy.integrable_mul hx

/-- Sharp Hölder estimate for the moment Hessian, including p = 2. -/
theorem rio_second_holder {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {p : ℝ} (hp : 2 ≤ p) {Y X : Ω → ℝ}
    (hY : MemLp Y (ENNReal.ofReal p) μ) (hX : MemLp X (ENNReal.ofReal p) μ) :
    (∫ ω, |Y ω| ^ (p - 2) * X ω ^ 2 ∂μ) ≤
      rioMoment μ p Y ^ ((p - 2) / p) * (eLpNorm X (ENNReal.ofReal p) μ).toReal ^ 2 := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  rcases hp.eq_or_lt with htwo | htwo
  · subst p
    simp only [sub_self, zero_div, Real.rpow_zero, one_mul]
    rw [rio_lpNorm_sq (by norm_num : (0 : ℝ) < 2) hX]
    simp only [div_self (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_one, rioMoment]
    apply le_of_eq
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ω => by
      change X ω ^ (2 : ℕ) = |X ω| ^ (2 : ℝ)
      rw [Real.rpow_two, sq_abs]
  · have hq : 0 < p - 2 := sub_pos.mpr htwo
    have hy := hY.norm_rpow_div (ENNReal.ofReal (p - 2))
    have hx := hX.norm_rpow_div (ENNReal.ofReal 2)
    rw [← ENNReal.ofReal_div_of_pos hq] at hy
    rw [← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)] at hx
    simp only [ENNReal.toReal_ofReal hq.le, Real.norm_eq_abs] at hy
    simp only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2), Real.norm_eq_abs,
      Real.rpow_two, sq_abs] at hx
    have hconj : (p / (p - 2)).HolderConjugate (p / 2) := by
      apply Real.holderConjugate_iff.mpr
      constructor
      · exact (one_lt_div hq).mpr (by linarith only [htwo])
      · field_simp
        ring
    have hh := integral_mul_le_Lp_mul_Lq_of_nonneg hconj
      (ae_of_all μ fun ω => Real.rpow_nonneg (abs_nonneg (Y ω)) _)
      (ae_of_all μ fun ω => sq_nonneg (X ω)) hy hx
    have hey (ω : Ω) : (|Y ω| ^ (p - 2)) ^ (p / (p - 2)) = |Y ω| ^ p := by
      rw [← Real.rpow_mul (abs_nonneg _)]
      congr 1
      field_simp
    have hex (ω : Ω) : (X ω ^ 2) ^ (p / 2) = |X ω| ^ p := by
      rw [← sq_abs, ← Real.rpow_two, ← Real.rpow_mul (abs_nonneg _)]
      congr 1
      ring
    have hqe : 1 / (p / (p - 2)) = (p - 2) / p := by field_simp
    have hre : 1 / (p / 2) = 2 / p := by field_simp
    simp only [hey, hex, hqe, hre] at hh
    rw [rio_lpNorm_sq hp0 hX]
    exact hh

/-- The first-variation pairing is integrable without a bounded-variable approximation. -/
theorem rio_integrable_first_product {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {p : ℝ} (hp : 2 ≤ p) {Y X : Ω → ℝ}
    (hY : MemLp Y (ENNReal.ofReal p) μ) (hX : MemLp X (ENNReal.ofReal p) μ) :
    Integrable (fun ω => p * |Y ω| ^ (p - 2) * Y ω * X ω) μ := by
  have hd := (integrable_power_mul (by linarith only [hp] : 1 < p)
    (fun ω => abs_nonneg (Y ω)) hY.norm hX.norm).const_mul p
  apply hd.mono'
    (((continuous_rio_power_derivative hp).comp_aestronglyMeasurable hY.aestronglyMeasurable).mul hX.aestronglyMeasurable)
  exact ae_of_all μ fun ω => by
    simpa only [Pi.mul_apply, Real.norm_eq_abs, mul_assoc] using rio_first_derivative_bound (p := p) (y := Y ω) (x := X ω) hp (le_refl |Y ω|)

/-- The Hessian pairing is integrable at the endpoint p = 2 as well. -/
theorem rio_integrable_second_product_ge_two {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {p : ℝ} (hp : 2 ≤ p) {Y X : Ω → ℝ}
    (hY : MemLp Y (ENNReal.ofReal p) μ) (hX : MemLp X (ENNReal.ofReal p) μ) :
    Integrable (fun ω => |Y ω| ^ (p - 2) * X ω ^ 2) μ := by
  rcases hp.eq_or_lt with he | he
  · subst p
    have hi : Integrable (fun ω => ‖X ω‖ ^ (2 : ℝ)) μ := by
      simpa only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2)] using hX.integrable_norm_rpow'
    simpa only [sub_self, Real.rpow_zero, one_mul, Real.norm_eq_abs, Real.rpow_two, sq_abs] using hi
  · exact rio_integrable_second_product he hY hX

end ASDExplicitGamma.Gaussian
