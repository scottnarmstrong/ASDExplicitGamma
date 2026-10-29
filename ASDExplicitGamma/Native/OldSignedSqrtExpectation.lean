module

public import ASDExplicitGamma.Native.BoundaryChargeNorm

/-! Probability-space square-root contraction with integrability proved. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory

/-- A nonnegative integrable energy has an integrable square root and the
constant-one expected square-root bound. -/
theorem old_signed_sqrt_expectation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : Integrable f μ) (hn : ∀ ω,0 ≤ f ω) :
    Integrable (fun ω => Real.sqrt (f ω)) μ ∧
      (∫ ω,Real.sqrt (f ω) ∂μ) ≤ Real.sqrt (∫ ω,f ω ∂μ) := by
  have hm : AEStronglyMeasurable (fun ω => Real.sqrt (f ω)) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hf.1
  have hs : Integrable (fun ω => (Real.sqrt (f ω))^2) μ := by
    simpa only [Real.sq_sqrt (hn _)] using hf
  have hLp := (memLp_two_iff_integrable_sq hm).mpr hs
  refine ⟨hLp.integrable (by norm_num),?_⟩
  have hh := native_boundary_mean_le_sqrt_second_moment μ
    (fun ω => Real.sqrt (f ω)) hLp (Filter.Eventually.of_forall (fun ω => Real.sqrt_nonneg (f ω)))
  simpa only [Real.sq_sqrt (hn _)] using hh

end ASDExplicitGamma.Native
