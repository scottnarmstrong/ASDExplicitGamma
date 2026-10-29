module

public import Mathlib

/-! Cauchy-Schwarz in the sample for square roots of integrable nonnegative functions. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open MeasureTheory

noncomputable section

theorem hotCov_sqrt_memLp_two {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {X : α → ℝ} (hX : Integrable X μ) (hX0 : ∀ ω, 0 ≤ X ω) :
    MemLp (fun ω => Real.sqrt (X ω)) 2 μ := by
  have hm : AEStronglyMeasurable (fun ω => Real.sqrt (X ω)) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hX.aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hm]
  refine hX.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp [Real.sq_sqrt (hX0 ω)]

theorem hotCov_cs_sqrt {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {X Y : α → ℝ} (hX : Integrable X μ) (hY : Integrable Y μ)
    (hX0 : ∀ ω, 0 ≤ X ω) (hY0 : ∀ ω, 0 ≤ Y ω) :
    Integrable (fun ω => Real.sqrt (X ω) * Real.sqrt (Y ω)) μ ∧
    (∫ ω, Real.sqrt (X ω) * Real.sqrt (Y ω) ∂μ) ≤
      Real.sqrt (∫ ω, X ω ∂μ) * Real.sqrt (∫ ω, Y ω ∂μ) := by
  have hf := hotCov_sqrt_memLp_two hX hX0
  have hg := hotCov_sqrt_memLp_two hY hY0
  refine ⟨hf.integrable_mul hg, ?_⟩
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) (p := 2) (q := 2)
    Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun ω => Real.sqrt_nonneg (X ω))
    (Filter.Eventually.of_forall fun ω => Real.sqrt_nonneg (Y ω))
    (by simpa using hf) (by simpa using hg)
  have e1 : (∫ ω, Real.sqrt (X ω) ^ (2 : ℝ) ∂μ) = ∫ ω, X ω ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp [Real.sq_sqrt (hX0 ω)]
  have e2 : (∫ ω, Real.sqrt (Y ω) ^ (2 : ℝ) ∂μ) = ∫ ω, Y ω ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp [Real.sq_sqrt (hY0 ω)]
  rw [e1, e2] at h
  simpa [Real.sqrt_eq_rpow] using h

end

end ASDExplicitGamma.Main
