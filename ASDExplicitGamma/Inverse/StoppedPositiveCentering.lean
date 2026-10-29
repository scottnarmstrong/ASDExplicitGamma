module

public import ASDExplicitGamma.Inverse.WeightedLocalizationLp

/-! The source one-sided centering at a moment upper bound retains its positive part. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory
open scoped ENNReal

/-- An upper bound for the mean justifies the source positive-part estimate;
it does not identify that upper bound with the actual expectation. -/
theorem weighted_positive_excess_le_centered {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) (X : I → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (v K : ℝ) (hwv : ∑ i, w i = v)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) ≤ K) (p : ℝ≥0∞) :
    eLpNorm (fun ω => max (∑ i, w i*X i ω-v*K) 0) p μ ≤
      eLpNorm (fun ω => ∑ i, w i*(X i ω-∫ ζ, X i ζ ∂μ)) p μ := by
  have hm : Measurable (fun ω => max (∑ i, w i*X i ω-v*K) 0) :=
    ((Finset.measurable_sum Finset.univ (fun i _ => (hX i).const_mul (w i))).sub_const (v*K)).max measurable_const
  have hmeans : (∑ i, w i*(∫ ω, X i ω ∂μ)) ≤ v*K := by
    calc
      _ ≤ ∑ i, w i*K := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hmean i) (hw i)
      _ = _ := by rw [← Finset.sum_mul,hwv]
  apply eLpNorm_mono hm.aestronglyMeasurable
  intro ω
  rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _),Real.norm_eq_abs]
  apply max_le
  · have he : (∑ i, w i*(X i ω-∫ ζ, X i ζ ∂μ)) =
        (∑ i, w i*X i ω)-(∑ i, w i*(∫ ζ, X i ζ ∂μ)) := by
      simp only [mul_sub,Finset.sum_sub_distrib]
    have hh : (∑ i, w i*X i ω)-v*K ≤ ∑ i, w i*(X i ω-∫ ζ, X i ζ ∂μ) := by
      rw [he]
      linarith only [hmeans]
    exact hh.trans (le_abs_self _)
  · exact abs_nonneg _

end ASDExplicitGamma.Inverse
