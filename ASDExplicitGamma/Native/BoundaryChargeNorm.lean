module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-! The direct-sum boundary charge used by the OLD q1 and parent branches.
The second component uses sqrt(2 xi), without a source-patch identity. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- On a probability space an annealed nonnegative amplitude is bounded by
its genuine second moment. -/
theorem native_boundary_mean_le_sqrt_second_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [hprob : IsProbabilityMeasure μ] (F : Ω → ℝ)
    (hF : MemLp F 2 μ) (hF0 : ∀ᵐ ω ∂μ, 0 ≤ F ω) :
    (∫ ω, F ω ∂μ) ≤ Real.sqrt (∫ ω, (F ω)^2 ∂μ) := by
  have hpq : Real.HolderConjugate 2 2 := Real.holderConjugate_iff.mpr ⟨by norm_num,by norm_num⟩
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg hpq hF0
    (Filter.Eventually.of_forall (fun _ => (by norm_num : (0:ℝ) ≤ 1)))
    (show MemLp F (ENNReal.ofReal 2) μ by simpa using hF)
    (memLp_const (1:ℝ) : MemLp (fun _ : Ω => (1:ℝ)) (ENNReal.ofReal 2) μ)
  simpa only [mul_one,Real.rpow_ofNat,integral_const,one_smul,probReal_univ,one_pow,Real.sqrt_one,
    Real.one_rpow,mul_one,← Real.sqrt_eq_rpow] using hh

end
end ASDExplicitGamma.Native
