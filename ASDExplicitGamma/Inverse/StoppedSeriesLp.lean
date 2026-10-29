module

public import ASDExplicitGamma.Inverse.HistoryLpSeries
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! Countable Minkowski for the complete density reset series. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory Filter
open scoped ENNReal

/-- A summable deterministic norm envelope controls the actual countable
pointwise series and proves its absolute convergence almost everywhere. -/
theorem countable_density_series_Lp {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
    (μ : Measure Ω) (p : ℝ≥0∞) (hp : 1 ≤ p) (f : I → Ω → ℝ)
    (hf : ∀ i, Measurable (f i)) (c : I → ℝ) (hc : ∀ i, 0 ≤ c i)
    (C : ℝ) (hs : HasSum c C) (hb : ∀ i, eLpNorm (f i) p μ ≤ ENNReal.ofReal (c i)) :
    (∀ᵐ ω ∂μ, Summable (fun i => ‖f i ω‖)) ∧
      eLpNorm (fun ω => ∑' i, f i ω) p μ ≤ ENNReal.ofReal C := by
  have hsum : (∑' i, eLpNorm (f i) p μ) ≤ ENNReal.ofReal C := by
    apply (ENNReal.tsum_le_tsum hb).trans_eq
    rw [← ENNReal.ofReal_tsum_of_nonneg hc hs.summable,hs.tsum_eq]
  have hfinite : (∑' i, eLpNorm (f i) p μ) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsum
  have hae := summable_norm_of_tsum_eLpNorm_ne_top hp hfinite
  refine ⟨hae,?_⟩
  apply le_trans _ hsum
  apply Lp.eLpNorm_le_of_ae_tendsto
    (f := fun s : Finset I => fun ω => ∑ i ∈ s, f i ω) (u := atTop)
  · apply Filter.Eventually.of_forall
    intro s
    have he : (∑ i ∈ s, f i) = (fun ω => ∑ i ∈ s, f i ω) := by
      funext ω
      simp only [Finset.sum_apply]
    rw [← he]
    exact (eLpNorm_sum_le hp).trans (ENNReal.sum_le_tsum s)
  · intro s
    exact (Finset.measurable_sum _ (fun i _ => hf i)).aestronglyMeasurable
  · exact (Measurable.tsum hf).aestronglyMeasurable
  · filter_upwards [hae] with ω hω
    exact (Summable.of_norm hω).hasSum

end ASDExplicitGamma.Inverse
