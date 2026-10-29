module

public import ASDExplicitGamma.Main.ELinearCellExpectation
public import ASDExplicitGamma.Main.ELinearCauchy

/-! Cauchy-Schwarz across the sample space for square-root majorants. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open MeasureTheory

noncomputable section

/-- `E[sqrt X sqrt Y] <= sqrt (E X) sqrt (E Y)` for a.e. nonnegative integrable
`X, Y`; the product is integrable. -/
theorem main_cauchy_sqrt_expectation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hX : Integrable X μ) (hY : Integrable Y μ)
    (hX0 : 0 ≤ᵐ[μ] X) (hY0 : 0 ≤ᵐ[μ] Y) :
    Integrable (fun ω => Real.sqrt (X ω) * Real.sqrt (Y ω)) μ ∧
      (∫ ω, Real.sqrt (X ω) * Real.sqrt (Y ω) ∂μ) ≤
        Real.sqrt (∫ ω, X ω ∂μ) * Real.sqrt (∫ ω, Y ω ∂μ) := by
  have hfm : AEStronglyMeasurable (fun ω => Real.sqrt (X ω)) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hX.aestronglyMeasurable
  have hgm : AEStronglyMeasurable (fun ω => Real.sqrt (Y ω)) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hY.aestronglyMeasurable
  have hsq (Z : Ω → ℝ) (hZ : Integrable Z μ) (hZ0 : 0 ≤ᵐ[μ] Z) :
      MemLp (fun ω => Real.sqrt (Z ω)) 2 μ := by
    have hm : AEStronglyMeasurable (fun ω => Real.sqrt (Z ω)) μ :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hZ.aestronglyMeasurable
    rw [memLp_two_iff_integrable_sq hm]
    refine hZ.congr ?_
    filter_upwards [hZ0] with ω hω
    rw [Real.sq_sqrt hω]
  have hf := hsq X hX hX0
  have hg := hsq Y hY hY0
  have hint : Integrable (fun ω => Real.sqrt (X ω) * Real.sqrt (Y ω)) μ :=
    hf.integrable_mul hg
  refine ⟨hint, ?_⟩
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) (p := 2) (q := 2)
    Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall (fun ω => Real.sqrt_nonneg _))
    (Filter.Eventually.of_forall (fun ω => Real.sqrt_nonneg _))
    (by simpa using hf) (by simpa using hg)
  have e1 : (∫ ω, Real.sqrt (X ω) ^ (2 : ℝ) ∂μ) = ∫ ω, X ω ∂μ := by
    apply integral_congr_ae
    filter_upwards [hX0] with ω hω
    rw [Real.rpow_two, Real.sq_sqrt hω]
  have e2 : (∫ ω, Real.sqrt (Y ω) ^ (2 : ℝ) ∂μ) = ∫ ω, Y ω ∂μ := by
    apply integral_congr_ae
    filter_upwards [hY0] with ω hω
    rw [Real.rpow_two, Real.sq_sqrt hω]
  rw [e1, e2] at hH
  simpa [Real.sqrt_eq_rpow] using hH

/-- Weighted cell majorant: the cell average of `G_U Z_U` is controlled, in
expectation, by `sqrt (E X) * sqrt (cell average of E Z_U^2)`, where `X`
majorizes the cell average of `G_U^2`. -/
theorem main_weighted_cell_majorant {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Finset ι)
    (G Z : ι → Ω → ℝ) (X : Ω → ℝ) (a c : ℝ)
    (hX : Integrable X μ) (hX0 : 0 ≤ᵐ[μ] X) (hXa : (∫ ω, X ω ∂μ) ≤ a)
    (hGX : ∀ᵐ ω ∂μ, finAvg S (fun U => G U ω ^ 2) ≤ X ω)
    (hZint : ∀ U ∈ S, Integrable (fun ω => Z U ω ^ 2) μ)
    (hZc : finAvg S (fun U => ∫ ω, Z U ω ^ 2 ∂μ) ≤ c)
    (hG0 : ∀ U ω, 0 ≤ G U ω) :
    ∃ Gb : Ω → ℝ, Integrable Gb μ ∧ 0 ≤ᵐ[μ] Gb ∧
      (∀ᵐ ω ∂μ, finAvg S (fun U => G U ω * Z U ω) ≤ Gb ω) ∧
      (∫ ω, Gb ω ∂μ) ≤ Real.sqrt a * Real.sqrt c := by
  let Y : Ω → ℝ := fun ω => finAvg S (fun U => Z U ω ^ 2)
  have hYint : Integrable Y μ := by
    unfold Y finAvg
    exact (integrable_finset_sum S hZint).const_mul _
  have hY0 : 0 ≤ᵐ[μ] Y := by
    refine Filter.Eventually.of_forall (fun ω => ?_)
    unfold Y finAvg
    exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun U _ => sq_nonneg _))
  have hYc : (∫ ω, Y ω ∂μ) ≤ c := by
    have : (∫ ω, Y ω ∂μ) = finAvg S (fun U => ∫ ω, Z U ω ^ 2 ∂μ) := by
      unfold Y finAvg
      rw [integral_const_mul, integral_finset_sum S hZint]
    rw [this]
    exact hZc
  obtain ⟨hint, hle⟩ := main_cauchy_sqrt_expectation μ X Y hX hYint hX0 hY0
  refine ⟨fun ω => Real.sqrt (X ω) * Real.sqrt (Y ω), hint,
    Filter.Eventually.of_forall (fun ω => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)),
    ?_, ?_⟩
  · filter_upwards [hGX] with ω hω
    refine (finAvg_mul_le S (fun U => G U ω) (fun U => Z U ω)).trans ?_
    exact mul_le_mul (Real.sqrt_le_sqrt hω) le_rfl (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · refine hle.trans ?_
    exact mul_le_mul (Real.sqrt_le_sqrt hXa) (Real.sqrt_le_sqrt hYc) (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _)

end
end ASDExplicitGamma.Main
