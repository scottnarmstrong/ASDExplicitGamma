module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-! Exact real-order Hölder payments for the actual localization mismatch event. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory
open scoped ENNReal

/-- Hölder on the literal mismatch event, with no independence hypothesis. -/
theorem indicator_holder {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (hX : AEStronglyMeasurable X μ)
    (E : Set Ω) (hE : MeasurableSet E) (p : ℝ) (hp : 0 < p) :
    eLpNorm (E.indicator X) (ENNReal.ofReal p) μ ≤
      eLpNorm X (ENNReal.ofReal (2*p)) μ*(μ E)^(1/(2*p)) := by
  let mismatchHolderTriple : ENNReal.HolderTriple (ENNReal.ofReal (2*p))
      (ENNReal.ofReal (2*p)) (ENNReal.ofReal p) := by
    constructor
    rw [← ENNReal.ofReal_inv_of_pos (mul_pos (by norm_num) hp),
      ← ENNReal.ofReal_inv_of_pos hp,← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    field_simp
    ring
  have hI : AEStronglyMeasurable (E.indicator (fun _ : Ω => (1:ℝ))) μ :=
    (measurable_const.indicator hE).aestronglyMeasurable
  have hh := eLpNorm_smul_le_mul_eLpNorm (p := ENNReal.ofReal (2*p))
    (q := ENNReal.ofReal (2*p)) (r := ENNReal.ofReal p) hX hI
  have he : (X • E.indicator (fun _ : Ω => (1:ℝ))) = E.indicator X := by
    funext ω
    by_cases hω : ω ∈ E
    · simp only [smul_eq_mul,Pi.mul_apply,Set.indicator,hω,ite_true,mul_one]
    · simp only [smul_eq_mul,Pi.mul_apply,Set.indicator,hω,ite_false,mul_zero]
  rw [he,eLpNorm_indicator_const hE.nullMeasurableSet
    (ENNReal.ofReal_ne_zero_iff.mpr (by positivity)) ENNReal.ofReal_ne_top,
    Real.enorm_eq_ofReal (by norm_num),ENNReal.ofReal_one,one_mul,
    ENNReal.toReal_ofReal (by positivity)] at hh
  exact hh

/-- The natural power uses exactly the real order p*m on its base field. -/
theorem nonnegative_power_eLpNorm {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (hX : AEStronglyMeasurable X μ)
    (hX0 : ∀ ω, 0 ≤ X ω) (m : ℕ) (hm : 0 < m) (p : ℝ) (hp : 0 ≤ p) :
    eLpNorm (fun ω => X ω^m) (ENNReal.ofReal p) μ =
      (eLpNorm X (ENNReal.ofReal (p*(m:ℝ))) μ)^m := by
  have he : (fun ω => X ω^m) = fun ω => ‖X ω‖^(m:ℝ) := by
    funext ω
    rw [Real.norm_eq_abs,abs_of_nonneg (hX0 ω),Real.rpow_natCast]
  rw [he,eLpNorm_norm_rpow X hX (by exact_mod_cast hm : (0:ℝ) < m),
    ← ENNReal.ofReal_mul hp,ENNReal.rpow_natCast]

/-- Exact real physical exponential payment for the mismatch event probability. -/
theorem mismatch_exponential_payment (N p : ℝ) :
    (ENNReal.ofReal (12000*Real.exp (-N/3)))^(1/(2*p):ℝ) =
      ENNReal.ofReal ((12000:ℝ)^(1/(2*p))*Real.exp (-N/(6*p))) := by
  rw [ENNReal.ofReal_rpow_of_pos (by positivity : (0:ℝ) < 12000*Real.exp (-N/3)),
    Real.mul_rpow (by norm_num : (0:ℝ) ≤ 12000) (Real.exp_pos _).le,
    ← Real.exp_mul]
  have he : (-N/3)*(1/(2*p)) = -N/(6*p) := by
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [he]

end ASDExplicitGamma.Inverse
