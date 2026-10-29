module

public import ASDExplicitGamma.Native.OldSignedSourceHistoryBudget

/-! Nonnegative actual half-trace and rare budgets. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Scalar Inverse Algsuperdiff.Section3 Numerics.Inverse
noncomputable section

/-- Each directional history budget is nonnegative on the actual time interval. -/
theorem old_signed_source_history_budget_nonneg (M : ABKModel 2) (n : ℤ)
    (U : TriadicCube 2) (t : ℝ) (ht : 0≤t ∧ t≤1) (j : ℕ) :
    0≤oldSignedSourceHistoryBudget M n U t j := by
  have ht0 : 0≤theta M := div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have htrace : 0≤∫ ω,rawWeakTraceSequence M n U t ω j ∂(Cutoff.cutoffSampleLaw M).toMeasure :=
    integral_nonneg (fun ω => raw_weak_trace_sequence_nonneg M n U t ht ω j)
  have hcap : 0≤(inverseBankCap .localInverse:ℝ) := by norm_num [inverseBankCap]
  have hres : 0≤(inverseBankReserve .localInverse:ℝ) := by norm_num [inverseBankReserve]
  have hMrat : 0 ≤ invTraceM := by rw [invTrace_coefficient.1]; positivity
  have hM0 : 0≤(invTraceM:ℝ) := by exact_mod_cast hMrat
  have hframe := (bankDepthFrame_pos M j).le
  unfold oldSignedSourceHistoryBudget inverseBankDepthReserve
  positivity

/-- The complete normalized directional budget is nonnegative, without
needing a moment or convergence estimate as a premise. -/
theorem old_signed_source_directional_budget_nonneg (M : ABKModel 2) (n : ℤ)
    (U : TriadicCube 2) (t : ℝ) (ht : 0≤t ∧ t≤1) :
    0≤(1-inverseHistoryDiscount^2)*
      ∑' j : ℕ,inverseHistoryDiscount^(2*j)*oldSignedSourceHistoryBudget M n U t j := by
  apply mul_nonneg
  · exact sub_nonneg.mpr (pow_le_one₀ inverse_history_discount_range.1.le inverse_history_discount_range.2.le)
  · exact tsum_nonneg (fun j => mul_nonneg (pow_nonneg inverse_history_discount_range.1.le _)
      (old_signed_source_history_budget_nonneg M n U t ht j))

end
end ASDExplicitGamma.Native
