module

public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! Infinite Minkowski with explicit finite extended norm budget.
The limit is the genuine pointwise sum almost everywhere. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory Filter
open scoped ENNReal

/-- A finite sum of extended Lp norms controls the norm of the infinite series. -/
theorem eLpNorm_tsum_le_of_finite {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (p : ℝ≥0∞) (hp : 1 ≤ p) (f : ℕ → Ω → ℝ)
    (hf : ∀ j, Measurable (f j)) (hbudget : (∑' j, eLpNorm (f j) p mu) ≠ ⊤) :
    eLpNorm (fun ω => ∑' j, f j ω) p mu ≤ ∑' j, eLpNorm (f j) p mu := by
  have hs := summable_norm_of_tsum_eLpNorm_ne_top hp hbudget
  apply Lp.eLpNorm_le_of_ae_tendsto
    (f := fun N ω => ∑ j ∈ Finset.range N, f j ω) (u := atTop)
  · apply Filter.Eventually.of_forall
    intro N
    calc
      _ ≤ ∑ j ∈ Finset.range N, eLpNorm (f j) p mu := by
        have he : (∑ j ∈ Finset.range N, f j) = (fun ω => ∑ j ∈ Finset.range N, f j ω) := by
          funext ω
          simp only [Finset.sum_apply]
        rw [← he]
        exact eLpNorm_sum_le hp
      _ ≤ ∑' j, eLpNorm (f j) p mu := ENNReal.sum_le_tsum (Finset.range N)
  · intro N
    exact (Finset.measurable_sum _ (fun j _ => hf j)).aestronglyMeasurable
  · exact (Measurable.tsum hf).aestronglyMeasurable
  · filter_upwards [hs] with ω hω
    exact (Summable.of_norm hω).tendsto_sum_tsum_nat

end ASDExplicitGamma.Inverse
