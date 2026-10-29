module

public import ASDExplicitGamma.Gaussian.RioSmoothness
public import Mathlib.Probability.ConditionalExpectation

/-! # GA-RIO: sharp type-two inequality for centered independent real variables -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ASDExplicitGamma.Gaussian

/-- The conditionally centered one-step inequality applies to an independent centered increment. -/
theorem rio_lp_smoothness_of_indep {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {p : ℝ} (hp : 2 ≤ p) {S X : Ω → ℝ}
    (hSm : Measurable S) (hXm : Measurable X)
    (hS : MemLp S (ENNReal.ofReal p) μ) (hX : MemLp X (ENNReal.ofReal p) μ)
    (hi : IndepFun X S μ) (hmean : ∫ ω, X ω ∂μ = 0) :
    (eLpNorm (fun ω => S ω + X ω) (ENNReal.ofReal p) μ).toReal ^ 2 ≤
      (eLpNorm S (ENNReal.ofReal p) μ).toReal ^ 2 +
        (p - 1) * (eLpNorm X (ENNReal.ofReal p) μ).toReal ^ 2 := by
  apply rio_lp_smoothness_given_variable μ hp hSm hS hX
  have hx : StronglyMeasurable[MeasurableSpace.comap X (borel ℝ)] X :=
    (@measurable_iff_comap_le Ω ℝ (MeasurableSpace.comap X (borel ℝ)) (borel ℝ) X).mpr le_rfl
      |>.stronglyMeasurable
  have hh := condExp_indep_eq hXm.comap_le hSm.comap_le hx ((IndepFun_iff_Indep X S μ).mp hi)
  filter_upwards [hh] with ω hω
  exact hω.trans hmean

/-- Rio's inequality for every finite family of independent centered real random variables,
at every real p ≥ 2, with the sharp type-two coefficient p−1. -/
theorem rio_independent_sum_sq_le {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {p : ℝ} (hp : 2 ≤ p)
    (X : ι → Ω → ℝ) (hXm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hX : ∀ i, MemLp (X i) (ENNReal.ofReal p) μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) (s : Finset ι) :
    (eLpNorm (fun ω => ∑ i ∈ s, X i ω) (ENNReal.ofReal p) μ).toReal ^ 2 ≤
      (p - 1) * ∑ i ∈ s, (eLpNorm (X i) (ENNReal.ofReal p) μ).toReal ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, mul_zero]
    change (eLpNorm (0 : Ω → ℝ) (ENNReal.ofReal p) μ).toReal ^ 2 ≤ 0
    rw [eLpNorm_zero, ENNReal.toReal_zero]
    norm_num
  | @insert i s his ih =>
    let S : Ω → ℝ := fun ω => ∑ j ∈ s, X j ω
    have hSm : Measurable S := Finset.measurable_sum _ (fun j _ => hXm j)
    have hSLp : MemLp S (ENNReal.ofReal p) μ := memLp_finsetSum s (fun j _ => hX j)
    have hfun : (∑ j ∈ s, X j) = S := by
      funext ω
      simp only [Finset.sum_apply]
      rfl
    have hInd : IndepFun (X i) S μ := by
      simpa only [hfun] using (hi.indepFun_finsetSum_of_notMem hXm his).symm
    have hstep := rio_lp_smoothness_of_indep μ hp hSm (hXm i) hSLp (hX i) hInd (hmean i)
    have hsum : (fun ω => ∑ j ∈ insert i s, X j ω) = fun ω => S ω + X i ω := by
      funext ω
      rw [Finset.sum_insert his]
      exact add_comm _ _
    rw [hsum, Finset.sum_insert his, mul_add]
    exact hstep.trans (by dsimp only [S] at *; linarith only [ih])

end ASDExplicitGamma.Gaussian
