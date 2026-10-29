module

public import ASDExplicitGamma.Gaussian.SupMeanFiniteConcentration

/-! Fatou's lemma retains sharp nonnegative integral bounds under almost-sure limits. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open MeasureTheory Filter
open scoped Topology ENNReal

/-- An almost-sure limit of nonnegative functions with uniformly bounded
integrals is integrable and retains that same bound. -/
theorem supMean_nonnegative_integral_limit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : ℕ → Ω → ℝ) (f : Ω → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ n, Integrable (F n) μ) (hF0 : ∀ n, 0 ≤ᵐ[μ] F n)
    (hf0 : 0 ≤ᵐ[μ] f) (hbound : ∀ n, (∫ ω, F n ω ∂μ) ≤ C)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => F n ω) atTop (𝓝 (f ω))) :
    Integrable f μ ∧ (∫ ω, f ω ∂μ) ≤ C := by
  have hm : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hF n).aestronglyMeasurable) hlim
  have hE (n : ℕ) : AEMeasurable (fun ω => ENNReal.ofReal (F n ω)) μ :=
    ENNReal.continuous_ofReal.measurable.comp_aemeasurable (hF n).aemeasurable
  have hEb (n : ℕ) : (∫⁻ ω, ENNReal.ofReal (F n ω) ∂μ) ≤ ENNReal.ofReal C := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hF n) (hF0 n)]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  have hfatou := lintegral_liminf_le' (u := atTop) hE
  have hupper : liminf (fun n => ∫⁻ ω, ENNReal.ofReal (F n ω) ∂μ) atTop ≤ ENNReal.ofReal C :=
    Filter.liminf_le_of_frequently_le (Filter.Frequently.of_forall hEb)
  have hb : (∫⁻ ω, ENNReal.ofReal (f ω) ∂μ) ≤ ENNReal.ofReal C := by
    calc
      _ = ∫⁻ ω, liminf (fun n => ENNReal.ofReal (F n ω)) atTop ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hlim] with ω hω
        exact (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hω).liminf_eq.symm
      _ ≤ _ := hfatou.trans hupper
  have hi : Integrable f μ :=
    ⟨hm, (hasFiniteIntegral_iff_ofReal hf0).mpr (hb.trans_lt (by simp))⟩
  refine ⟨hi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hf0 hm]
  exact (ENNReal.toReal_mono (by simp) hb).trans_eq (ENNReal.toReal_ofReal hC)

end ASDExplicitGamma.Gaussian
