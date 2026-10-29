module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! A finite convex exponential budget permits arbitrary dependence between mark groups. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory
open scoped BigOperators

/-- Convexity combines independently estimated groups without any independence
between the groups. A spare zero group can retain any unused weight. -/
theorem correlated_groups_exp_bound {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hwsum : ∑ i, w i = 1) (Y : I → Ω → ℝ) (hY : ∀ i, Measurable (Y i))
    (hInt : ∀ i, Integrable (fun ω => Real.exp (Y i ω)) μ)
    (C : ℝ) (hC : ∀ i, (∫ ω, Real.exp (Y i ω) ∂μ) ≤ C) :
    Integrable (fun ω => Real.exp (∑ i, w i*Y i ω)) μ ∧
    (∫ ω, Real.exp (∑ i, w i*Y i ω) ∂μ) ≤ C := by
  have hpoint (ω : Ω) : Real.exp (∑ i, w i*Y i ω) ≤ ∑ i, w i*Real.exp (Y i ω) := by
    simpa only [smul_eq_mul] using convexOn_exp.map_sum_le
      (fun i _ => hw i) hwsum (fun i _ => Set.mem_univ (Y i ω))
  have hi : Integrable (fun ω => ∑ i, w i*Real.exp (Y i ω)) μ :=
    integrable_finsetSum Finset.univ (fun i _ => (hInt i).const_mul (w i))
  have hmeas : Measurable (fun ω => Real.exp (∑ i, w i*Y i ω)) :=
    (Finset.measurable_sum Finset.univ (fun i _ => measurable_const.mul (hY i))).exp
  have hf : Integrable (fun ω => Real.exp (∑ i, w i*Y i ω)) μ := by
    apply hi.mono' hmeas.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro ω
    simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using hpoint ω
  refine ⟨hf,(integral_mono hf hi hpoint).trans ?_⟩
  rw [integral_finsetSum Finset.univ (fun i _ => (hInt i).const_mul (w i))]
  simp only [integral_const_mul]
  calc
    _ ≤ ∑ i, w i*C := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hC i) (hw i)
    _ = C := by rw [← Finset.sum_mul,hwsum,one_mul]

end ASDExplicitGamma.Inverse
