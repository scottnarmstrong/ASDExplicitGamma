module

public import ASDExplicitGamma.Inverse.WeightedLocalizationLp
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! A one-sided exponential moment suffices for nonnegative real-order norms. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory
open scoped ENNReal

/-- With E exp(X/8)<=2 and X>=0, every real p>=1 has norm at most 16p.
This consumes the existing real-order MGF lemma without rounding p. -/
theorem nonnegative_exp_moment_Lp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (hX0 : ∀ ω, 0 ≤ X ω) (hi : Integrable (fun ω => Real.exp (X ω/8)) μ)
    (hb : (∫ ω, Real.exp (X ω/8) ∂μ) ≤ 2) (p : ℝ) (hp : 1 ≤ p) :
    eLpNorm X (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (16*p) := by
  have he : (fun ω => Real.exp ((1/8:ℝ)*X ω)) = (fun ω => Real.exp (X ω/8)) := by
    funext ω
    congr 1
    ring
  have hn (ω : Ω) : Real.exp (-(1/8:ℝ)*X ω) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (hX0 ω))
  have hmN : Measurable (fun ω => Real.exp (-(1/8:ℝ)*X ω)) := (hX.const_mul _).exp
  have hiN : Integrable (fun ω => Real.exp (-(1/8:ℝ)*X ω)) μ := by
    apply (integrable_const (1:ℝ)).mono' hmN.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro ω
    simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using hn ω
  have hN : (∫ ω, Real.exp (-(1/8:ℝ)*X ω) ∂μ) ≤ 1 := by
    have hh := integral_mono hiN (integrable_const (1:ℝ)) hn
    simpa only [integral_const,probReal_univ,one_smul] using! hh
  have htwo : (2:ℝ) ≤ Real.exp p :=
    Real.exp_one_gt_two.le.trans (Real.exp_le_exp.mpr hp)
  have hP : (∫ ω, Real.exp ((1/8:ℝ)*X ω) ∂μ) ≤ Real.exp p := by
    rw [he]
    exact hb.trans htwo
  have hNN : (∫ ω, Real.exp (-(1/8:ℝ)*X ω) ∂μ) ≤ Real.exp p :=
    hN.trans ((by norm_num : (1:ℝ) ≤ 2).trans htwo)
  have hiP : Integrable (fun ω => Real.exp ((1/8:ℝ)*X ω)) μ := by rw [he]; exact hi
  have hh := localization_eLpNorm_of_exp_bounds μ X hX.aemeasurable p (1/8) hp (by norm_num)
    hiP hiN hP hNN
  convert hh using 1
  congr 1
  ring

end ASDExplicitGamma.Inverse
