module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Positive series with integrable terms and a summable expectation budget. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory Filter
open scoped ENNReal Topology

/-- A complete nonnegative random series has a genuine finite integral when
its termwise expectations have a summable budget. Pointwise convergence is
retained explicitly, so a divergent real tsum cannot vanish by convention. -/
theorem old_signed_nonnegative_series_integral
    {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
    (μ : Measure Ω) (f : I → Ω → ℝ) (C : I → ℝ)
    (hf : ∀ j,Integrable (f j) μ) (hn : ∀ j ω,0 ≤ f j ω)
    (hs : ∀ ω,Summable (fun j => f j ω)) (hC : Summable C)
    (hb : ∀ j,(∫ ω,f j ω ∂μ) ≤ C j) :
    Integrable (fun ω => ∑' j,f j ω) μ ∧
      (∫ ω,∑' j,f j ω ∂μ) ≤ ∑' j,C j := by
  classical
  have hI : Summable (fun j => ∫ ω,f j ω ∂μ) :=
    Summable.of_nonneg_of_le (fun j => integral_nonneg (hn j)) hb hC
  have hm : AEStronglyMeasurable (fun ω => ∑' j,f j ω) μ := by
    apply aestronglyMeasurable_of_tendsto_ae atTop
      (fun s : Finset I => s.aestronglyMeasurable_fun_sum (fun j _ => (hf j).1))
    exact Eventually.of_forall (fun ω => (hs ω).hasSum)
  have he : (∫⁻ ω,ENNReal.ofReal (∑' j,f j ω) ∂μ)=
      ENNReal.ofReal (∑' j,∫ ω,f j ω ∂μ) := by
    simp_rw [ENNReal.ofReal_tsum_of_nonneg (fun j => hn j _) (hs _)]
    rw [lintegral_tsum (fun j => (hf j).aestronglyMeasurable.aemeasurable.ennreal_ofReal)]
    simp_rw [←ofReal_integral_eq_lintegral_ofReal (hf _) (Eventually.of_forall (hn _))]
    exact (ENNReal.ofReal_tsum_of_nonneg (fun j => integral_nonneg (hn j)) hI).symm
  have hi : Integrable (fun ω => ∑' j,f j ω) μ :=
    (lintegral_ofReal_ne_top_iff_integrable hm
      (Eventually.of_forall (fun ω => tsum_nonneg (fun j => hn j ω)))).mp
      (by rw [he]; exact ENNReal.ofReal_ne_top)
  have hnorm : Summable (fun j => ∫ ω,‖f j ω‖ ∂μ) := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hn _ _)] using hI
  refine ⟨hi,?_⟩
  rw [←integral_tsum_of_summable_integral_norm hf hnorm]
  exact hI.tsum_le_tsum hb hC

end ASDExplicitGamma.Native
