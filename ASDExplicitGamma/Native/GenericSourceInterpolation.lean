module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! Actual Lp interpolation for the two finite-Holder minima.
These are function-space estimates, separate from scalar profile comparisons. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- The exact two-moment interpolation, with both probability norms taken
before any source-profile substitution. It also holds for general measures. -/
theorem native_source_eLpNorm_interpolate {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (hf : AEStronglyMeasurable f μ)
    (a b q : ℝ) (ha : 0 < a) (hab : a < b) (haq : a ≤ q) (hqb : q ≤ b)
    (A B : ℝ≥0∞) (hA : eLpNorm' f a μ ≤ A) (hB : eLpNorm' f b μ ≤ B) :
    eLpNorm' f q μ ≤ A^(a*(b-q)/(q*(b-a)))*B^(b*(q-a)/(q*(b-a))) := by
  let alpha : ℝ := (b-q)/(b-a)
  let beta : ℝ := (q-a)/(b-a)
  have hden : 0 < b-a := sub_pos.mpr hab
  have hq : 0 < q := ha.trans_le haq
  have hb : 0 < b := ha.trans hab
  have halpha : 0 ≤ alpha := div_nonneg (sub_nonneg.mpr hqb) hden.le
  have hbeta : 0 ≤ beta := div_nonneg (sub_nonneg.mpr haq) hden.le
  have hsum : alpha+beta=1 := by dsimp only [alpha,beta]; field_simp; ring
  have hmoment : a*alpha+b*beta=q := by dsimp only [alpha,beta]; field_simp; ring
  have hfun : (fun ω => (‖f ω‖ₑ^a)^alpha*(‖f ω‖ₑ^b)^beta) =
      (fun ω => ‖f ω‖ₑ^q) := by
    funext ω
    rw [← ENNReal.rpow_mul,← ENNReal.rpow_mul,
      ← ENNReal.rpow_add_of_nonneg _ _ (mul_nonneg ha.le halpha) (mul_nonneg hb.le hbeta),hmoment]
  have hholder := ENNReal.lintegral_mul_norm_pow_le (hf.enorm.pow_const a)
    (hf.enorm.pow_const b) halpha hbeta hsum
  have hma : (∫⁻ ω, ‖f ω‖ₑ^a ∂μ) ≤ A^a := by
    rw [lintegral_rpow_enorm_eq_rpow_eLpNorm' ha]
    exact ENNReal.rpow_le_rpow hA ha.le
  have hmb : (∫⁻ ω, ‖f ω‖ₑ^b ∂μ) ≤ B^b := by
    rw [lintegral_rpow_enorm_eq_rpow_eLpNorm' hb]
    exact ENNReal.rpow_le_rpow hB hb.le
  have hm : (∫⁻ ω, ‖f ω‖ₑ^q ∂μ) ≤ (A^a)^alpha*(B^b)^beta := by
    rw [← hfun]
    exact hholder.trans (mul_le_mul' (ENNReal.rpow_le_rpow hma halpha)
      (ENNReal.rpow_le_rpow hmb hbeta))
  have hh := ENNReal.rpow_le_rpow hm (by positivity : 0 ≤ 1/q)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ 1/q),
    ← ENNReal.rpow_mul,← ENNReal.rpow_mul,← ENNReal.rpow_mul,← ENNReal.rpow_mul] at hh
  have heA : a*(alpha*(1/q))=a*(b-q)/(q*(b-a)) := by dsimp only [alpha]; field_simp
  have heB : b*(beta*(1/q))=b*(q-a)/(q*(b-a)) := by dsimp only [beta]; field_simp
  rw [heA,heB] at hh
  simpa only [eLpNorm',one_div] using hh

end
end ASDExplicitGamma.Native
