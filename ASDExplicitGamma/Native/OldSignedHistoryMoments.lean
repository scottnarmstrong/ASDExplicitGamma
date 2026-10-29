module

public import ASDExplicitGamma.Native.OldSignedSqrtProductExpectation
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! Sharp probability-space moments for the OLD matrix-history majorant. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- The real L2 norm is the square root of the actual second moment. -/
theorem old_signed_lpNorm_two {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (hf : MemLp f 2 μ) :
    lpNorm f 2 μ = Real.sqrt (∫ ω, (f ω)^2 ∂μ) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
    hf.aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_ofNat, Real.norm_eq_abs,
    sq_abs, ← Real.sqrt_eq_rpow, one_div]

/-- A nonnegative L2 history pays its first and second moments with no
replacement of the correlated probability law. -/
theorem old_signed_history_first_second_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H : Ω → ℝ) (C : ℝ)
    (hH : MemLp H 2 μ) (hH0 : ∀ ω,0≤H ω) (hC : 0≤C)
    (hcap : lpNorm H 2 μ ≤ C) :
    (∫ ω,H ω ∂μ) ≤ C ∧ (∫ ω,(H ω)^2 ∂μ) ≤ C^2 := by
  have hs := old_signed_lpNorm_two μ H hH
  have hsq : (∫ ω,(H ω)^2 ∂μ) = (lpNorm H 2 μ)^2 := by
    rw [hs, Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _))]
  refine ⟨?_, ?_⟩
  · exact (native_boundary_mean_le_sqrt_second_moment μ H hH
      (Filter.Eventually.of_forall hH0)).trans (hs ▸ hcap)
  · rw [hsq]
    exact (sq_le_sq₀ lpNorm_nonneg hC).mpr hcap

/-- The square root of an integrable energy has its exact L2 norm. -/
theorem old_signed_sqrt_L2 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (H : Ω → ℝ) (hH : Integrable H μ) (hH0 : ∀ ω,0≤H ω) :
    MemLp (fun ω => Real.sqrt (H ω)) 2 μ ∧
    lpNorm (fun ω => Real.sqrt (H ω)) 2 μ = Real.sqrt (∫ ω,H ω ∂μ) := by
  have hh : MemLp (fun ω => Real.sqrt (H ω)) 2 μ :=
    (memLp_two_iff_integrable_sq
      (Real.continuous_sqrt.comp_aestronglyMeasurable hH.1)).mpr
      (by simpa only [Real.sq_sqrt (hH0 _)] using hH)
  refine ⟨hh, ?_⟩
  rw [old_signed_lpNorm_two μ _ hh]
  simp only [Real.sq_sqrt (hH0 _)]

end
end ASDExplicitGamma.Native
