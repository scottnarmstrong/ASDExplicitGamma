module

public import ASDExplicitGamma.Native.OldSignedNonnegativeSeriesIntegral

/-! Actual integrability and a.e. convergence of the positive infinite
payments, derived from a summable expectation budget. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

/-- A summable positive expectation budget proves the convergence needed
before a real tsum can be used. No pointwise convergence premise is needed. -/
theorem old_hessian_positive_series_integral
    {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
    (μ : Measure Ω) (f : I → Ω → ℝ) (C : I → ℝ)
    (hf : ∀ j,Integrable (f j) μ) (hn : ∀ j ω,0≤f j ω)
    (hC : Summable C) (hb : ∀ j,(∫ ω,f j ω ∂μ)≤C j) :
    (∀ᵐ ω ∂μ,Summable (fun j => f j ω)) ∧
      Integrable (fun ω => ∑' j,f j ω) μ ∧
      (∫ ω,∑' j,f j ω ∂μ)≤∑' j,C j := by
  classical
  have hI : Summable (fun j => ∫ ω,f j ω ∂μ) :=
    Summable.of_nonneg_of_le (fun j => integral_nonneg (hn j)) hb hC
  have he : (∫⁻ ω,∑' j,ENNReal.ofReal (f j ω) ∂μ)=
      ENNReal.ofReal (∑' j,∫ ω,f j ω ∂μ) := by
    rw [lintegral_tsum (fun j => (hf j).aestronglyMeasurable.aemeasurable.ennreal_ofReal)]
    simp_rw [←ofReal_integral_eq_lintegral_ofReal (hf _) (Eventually.of_forall (hn _))]
    exact (ENNReal.ofReal_tsum_of_nonneg (fun j => integral_nonneg (hn j)) hI).symm
  have hfinite : ∀ᵐ ω ∂μ,(∑' j,ENNReal.ofReal (f j ω))<⊤ :=
    ae_lt_top' (AEMeasurable.tsum (fun j => (hf j).aestronglyMeasurable.aemeasurable.ennreal_ofReal))
      (by rw [he]; exact ENNReal.ofReal_ne_top)
  have hs : ∀ᵐ ω ∂μ,Summable (fun j => f j ω) := by
    filter_upwards [hfinite] with ω hω
    have hh := ENNReal.summable_toReal hω.ne
    simpa only [ENNReal.toReal_ofReal (hn _ _)] using hh
  have hm : AEStronglyMeasurable (fun ω => ∑' j,f j ω) μ := by
    apply aestronglyMeasurable_of_tendsto_ae atTop
      (fun s : Finset I => s.aestronglyMeasurable_fun_sum (fun j _ => (hf j).1))
    filter_upwards [hs] with ω hω
    exact hω.hasSum
  have hsumENN : ∀ᵐ ω ∂μ,ENNReal.ofReal (∑' j,f j ω)=∑' j,ENNReal.ofReal (f j ω) := by
    filter_upwards [hs] with ω hω
    exact ENNReal.ofReal_tsum_of_nonneg (fun j => hn j ω) hω
  have hi : Integrable (fun ω => ∑' j,f j ω) μ :=
    (lintegral_ofReal_ne_top_iff_integrable hm
      (Eventually.of_forall (fun ω => tsum_nonneg (fun j => hn j ω)))).mp (by
        rw [lintegral_congr_ae hsumENN,he]
        exact ENNReal.ofReal_ne_top)
  refine ⟨hs,hi,?_⟩
  rw [←integral_tsum_of_summable_integral_norm hf
    (by simpa only [Real.norm_eq_abs,abs_of_nonneg (hn _ _)] using hI)]
  exact hI.tsum_le_tsum hb hC

end
end ASDExplicitGamma.Scalar
