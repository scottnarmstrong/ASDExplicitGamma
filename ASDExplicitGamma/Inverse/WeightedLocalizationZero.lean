module

public import ASDExplicitGamma.Inverse.WeightedLocalizationIndependent

/-! Empty and zero-variance color classes introduce no strict-positivity assumptions. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization.IndependentSums MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- A finite family with a zero absolute bound sums to zero almost everywhere. -/
theorem localization_sum_zero_of_abs_bound {Ω ι : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (X : ι → Ω → ℝ) (s : Finset ι)
    (hbound : ∀ i ∈ s, ∀ᵐ ω ∂mu, |X i ω| ≤ 0) :
    (fun ω => ∑ i ∈ s, X i ω) =ᵐ[mu] 0 := by
  filter_upwards [(s.eventually_all).mpr hbound] with ω hω
  change (∑ i ∈ s, X i ω) = 0
  apply Finset.sum_eq_zero
  intro i hi
  exact abs_nonpos_iff.mp (hω i hi)

/-- A bounded family whose total second moment vanishes sums to zero almost everywhere. -/
theorem localization_sum_zero_of_variance_bound {Ω ι : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (X : ι → Ω → ℝ) (s : Finset ι)
    (hm : ∀ i, Measurable (X i)) (b : ℝ)
    (hbound : ∀ i ∈ s, ∀ᵐ ω ∂mu, |X i ω| ≤ b)
    (hvar : (∑ i ∈ s, moment (X i) 2 mu) ≤ 0) :
    (fun ω => ∑ i ∈ s, X i ω) =ᵐ[mu] 0 := by
  have hi0 (i : ι) (hi : i ∈ s) : X i =ᵐ[mu] 0 := by
    have hnonneg (j : ι) : 0 ≤ moment (X j) 2 mu := integral_nonneg (fun ω => sq_nonneg _)
    have hle := Finset.single_le_sum (fun j (_ : j ∈ s) => hnonneg j) hi
    have he : moment (X i) 2 mu = 0 := le_antisymm (hle.trans hvar) (hnonneg i)
    have hint := integrable_pow_two_of_abs_le_const (hm i).aemeasurable (hbound i hi)
    have hz := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (X i ω)) hint).mp he
    filter_upwards [hz] with ω hω
    exact sq_eq_zero_iff.mp hω
  filter_upwards [(s.eventually_all).mpr hi0] with ω hω
  change (∑ i ∈ s, X i ω) = 0
  exact Finset.sum_eq_zero (fun i hi => hω i hi)

/-- The real-order independent-sum bound includes zero variance and empty color
classes. Its structural bounds may be non-strict. -/
theorem localization_independent_Lp_nonneg {Ω ι : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (X : ι → Ω → ℝ) (s : Finset ι)
    (hind : iIndepFun X mu) (hm : ∀ i, Measurable (X i))
    (b V p : ℝ) (hb : 0 ≤ b) (hV : 0 ≤ V) (hp : 1 ≤ p)
    (hbound : ∀ i ∈ s, ∀ᵐ ω ∂mu, |X i ω| ≤ b)
    (hmean : ∀ i ∈ s, ∫ ω, X i ω ∂mu = 0)
    (hvar : (∑ i ∈ s, moment (X i) 2 mu) ≤ V) :
    eLpNorm (fun ω => ∑ i ∈ s, X i ω) (ENNReal.ofReal p) mu ≤
      ENNReal.ofReal (2 * Real.sqrt V * Real.sqrt p + 2 * b * p) := by
  rcases hb.eq_or_lt with he | hb
  · have hz := localization_sum_zero_of_abs_bound mu X s (by simpa only [← he] using hbound)
    rw [eLpNorm_congr_ae hz, eLpNorm_zero]
    exact zero_le
  rcases hV.eq_or_lt with he | hV
  · have hz := localization_sum_zero_of_variance_bound mu X s hm b hbound (by simpa only [← he] using hvar)
    rw [eLpNorm_congr_ae hz, eLpNorm_zero]
    exact zero_le
  exact localization_independent_Lp mu X s hind hm b V p hb hV hp hbound hmean hvar

end ASDExplicitGamma.Inverse
