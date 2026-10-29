module

public import ASDExplicitGamma.Scalar.PsdTiledChaos
public import ASDExplicitGamma.Scalar.ChaosHilbertEnvelope
public import ASDExplicitGamma.Gaussian.ModelHeatLaw
public import Homogenization.Geometry.TriadicCube

/-! Fibrewise comparison of `L^q` norms on a product law, and the old/fresh chaos step. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open MeasureTheory ProbabilityTheory ASDExplicitGamma.Gaussian
open scoped ENNReal

/-- Minkowski/Fubini: fibrewise `L^q` bounds integrate to a product `L^q` bound. -/
theorem eLpNorm_prod_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ν : Measure α) [SFinite ν] (μ : Measure β) [SFinite μ]
    (F : α → β → ℝ) (hF : Measurable (fun z : α × β => F z.1 z.2))
    (q : ℝ≥0∞) (hq0 : q ≠ 0) (hqtop : q ≠ ∞) (g : α → ℝ≥0∞)
    (hfib : ∀ a, eLpNorm (F a) q μ ≤ g a) :
    eLpNorm (fun z : α × β => F z.1 z.2) q (ν.prod μ) ≤
      (∫⁻ a, g a ^ q.toReal ∂ν) ^ (1 / q.toReal) := by
  have hqr : 0 < q.toReal := ENNReal.toReal_pos hq0 hqtop
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqtop hF.aestronglyMeasurable]
  have hmeas : Measurable (fun z : α × β => ‖F z.1 z.2‖ₑ ^ q.toReal) :=
    (hF.enorm).pow_const _
  rw [lintegral_prod _ hmeas.aemeasurable]
  refine ENNReal.rpow_le_rpow ?_ (by positivity)
  refine lintegral_mono fun a => ?_
  have h1 := hfib a
  have hFa : Measurable (F a) := by
    have : Measurable (fun b => F a b) := hF.comp (measurable_const.prodMk measurable_id)
    exact this
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqtop hFa.aestronglyMeasurable] at h1
  have h2 := ENNReal.rpow_le_rpow h1 hqr.le
  rw [← ENNReal.rpow_mul] at h2
  simpa [one_div, inv_mul_cancel₀ hqr.ne'] using h2

end ASDExplicitGamma.Scalar
