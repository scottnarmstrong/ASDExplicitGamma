module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! # Uniform nonnegative moment bounds pass to almost-everywhere limits -/

@[expose] public section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace ASDExplicitGamma.Gaussian

/-- Fatou gives both integrability and the same uniform bound, without a majorant. -/
theorem integrable_integral_le_of_ae_tendsto_nonneg {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {f : ℕ → Ω → ℝ} {g : Ω → ℝ} {C : ℝ}
    (hf : ∀ n, Integrable (f n) μ) (hf0 : ∀ n, 0 ≤ᵐ[μ] f n)
    (hg : AEStronglyMeasurable g μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (hC : ∀ n, ∫ x, f n x ∂μ ≤ C) :
    Integrable g μ ∧ ∫ x, g x ∂μ ≤ C := by
  have hg0 : 0 ≤ᵐ[μ] g := by
    filter_upwards [hlim, ae_all_iff.mpr hf0] with x hx hx0
    exact ge_of_tendsto hx (Eventually.of_forall hx0)
  have hbound : (∫⁻ x, ENNReal.ofReal (g x) ∂μ) ≤ ENNReal.ofReal C := by
    have he : (∫⁻ x, ENNReal.ofReal (g x) ∂μ) =
        ∫⁻ x, liminf (fun n => ENNReal.ofReal (f n x)) atTop ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hlim] with x hx
      exact ((ENNReal.continuous_ofReal.tendsto _).comp hx).liminf_eq.symm
    rw [he]
    apply (lintegral_liminf_le' fun n => (hf n).aestronglyMeasurable.aemeasurable.ennreal_ofReal).trans
    apply liminf_le_of_frequently_le'
    exact Frequently.of_forall fun n => by
      rw [← ofReal_integral_eq_lintegral_ofReal (hf n) (hf0 n)]
      exact ENNReal.ofReal_le_ofReal (hC n)
  have hgi : Integrable g μ := by
    refine ⟨hg, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hg0]
    exact hbound.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hgi, ?_⟩
  have hC0 : 0 ≤ C := (integral_nonneg_of_ae (hf0 0)).trans (hC 0)
  rw [← ofReal_integral_eq_lintegral_ofReal hgi hg0] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff hC0).mp hbound

end ASDExplicitGamma.Gaussian
