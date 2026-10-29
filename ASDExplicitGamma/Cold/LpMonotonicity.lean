module

public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-! # Real Lp norm monotonicity for actual nonnegative cold traces -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ASDExplicitGamma.Cold

/-- Almost-everywhere norm domination gives real Lp domination when the majorant is finite. -/
theorem cold_lpNorm_mono_ae {Ω : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    {f g : Ω → ℝ} {p : ℝ≥0∞} (hg : MemLp g p ℙ)
    (h : ∀ᵐ ω ∂ℙ, ‖f ω‖ ≤ ‖g ω‖) : lpNorm f p ℙ ≤ lpNorm g p ℙ := by
  by_cases hf : AEStronglyMeasurable f ℙ
  · exact ENNReal.toReal_mono hg.eLpNorm_ne_top (eLpNorm_mono_ae hf h)
  · rw [lpNorm_of_not_aestronglyMeasurable hf]
    exact lpNorm_nonneg

/-- A pathwise nonnegative subadditive trace is bounded by the L20 norm of its actual average. -/
theorem cold_nonnegative_trace_lpNorm_le {Ω : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    {T A : Ω → ℝ} (hA : MemLp A 20 ℙ)
    (hT : ∀ᵐ ω ∂ℙ, 0 ≤ T ω) (hsub : ∀ᵐ ω ∂ℙ, T ω ≤ A ω) :
    lpNorm T 20 ℙ ≤ lpNorm A 20 ℙ := by
  apply cold_lpNorm_mono_ae hA
  filter_upwards [hT,hsub] with ω hn hs
  rw [Real.norm_eq_abs,abs_of_nonneg hn,Real.norm_eq_abs,abs_of_nonneg (hn.trans hs)]
  exact hs

end ASDExplicitGamma.Cold
