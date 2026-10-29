module

public import ASDExplicitGamma.Native.OldSignedDepthSeriesArithmetic
public import ASDExplicitGamma.Native.OldSignedSourceDirectionalPayment

/-! Finite complete expectation budgets for the actual directional history. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Scalar Inverse Algsuperdiff.Section3 Numerics.Inverse
open scoped ENNReal
noncomputable section

/-- The deterministic half-trace contribution plus the correlated rare payment. -/
def oldSignedSourceHistoryBudget (M : ABKModel 2) (n : ℤ) (U : TriadicCube 2) (t : ℝ) (j : ℕ) : ℝ :=
  (inverseBankCap .localInverse:ℝ)*bankDepthFrame M j/2*
    (∫ ω,rawWeakTraceSequence M n U t ω j
      ∂(Cutoff.cutoffSampleLaw M).toMeasure)+
    inverseBankDepthReserve .localInverse M j*
      (theta M*(invTraceM:ℝ)*(1+(j:ℝ))^2*(3:ℝ)^(6*gammaZero*j))

/-- The raw L2 producer also pays the genuine first trace moment. -/
theorem old_signed_source_trace_mean_bound
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (r : ℕ) (hr : r ≤ 5)
    (U : TriadicCube 2) (hU : U.scale=n-(r:ℤ)) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (hstates : ∀ l ≤ n,nativeInductionState M h l) (j : ℕ) :
    (∫ ω,rawWeakTraceSequence M n U t ω j
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        theta M*(invTraceM:ℝ)*(1+(j:ℝ))^2*(3:ℝ)^(6*gammaZero*j) := by
  have htrace := old_signed_source_cell_trace_sequence_L2 M h hM hg n r hr t ht hstates U hU j
  have ht0 : 0 ≤ theta M := div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have hMrat : 0 ≤ invTraceM := by rw [invTrace_coefficient.1]; positivity
  have hM0 : 0 ≤ (invTraceM:ℝ) := by exact_mod_cast hMrat
  have hh := old_signed_rare_trace_integrable_bound (fun _ : Cutoff.CutoffSample 2 => (0:ℝ))
    (fun ω => rawWeakTraceSequence M n U t ω j) 0
    (theta M*(invTraceM:ℝ)*(1+(j:ℝ))^2*(3:ℝ)^(6*gammaZero*j)) 0
    (by norm_num) (by norm_num) (by positivity) (fun _ => le_rfl)
    (fun ω => raw_weak_trace_sequence_nonneg M n U t ht ω j)
    aestronglyMeasurable_const (old_signed_source_trace_integrable M n U t ht j).1
    (by simp) htrace
  simpa only [pow_zero,one_mul] using hh.2

/-- The full half-trace/rare budget is summable with the squared weak weights. -/
theorem old_signed_source_history_budget_summable
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (r : ℕ) (hr : r ≤ 5)
    (U : TriadicCube 2) (hU : U.scale=n-(r:ℤ)) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (hstates : ∀ l ≤ n,nativeInductionState M h l) :
    Summable (fun j : ℕ => inverseHistoryDiscount^(2*j)*oldSignedSourceHistoryBudget M n U t j) := by
  have hbase : Summable (fun j : ℕ => inverseHistoryDiscount^(2*j)*bankDepthFrame M j*
      (∫ ω,rawWeakTraceSequence M n U t ω j
        ∂(Cutoff.cutoffSampleLaw M).toMeasure)) := by
    apply Summable.of_nonneg_of_le _ _ (old_signed_depth_trace_budget_summable M hg)
    · intro j
      exact mul_nonneg (mul_nonneg (pow_nonneg inverse_history_discount_range.1.le _)
        (bankDepthFrame_pos M j).le)
        (integral_nonneg (fun ω => raw_weak_trace_sequence_nonneg M n U t ht ω j))
    · intro j
      exact mul_le_mul_of_nonneg_left
        (old_signed_source_trace_mean_bound M h hM hg n r hr U hU t ht hstates j)
        (mul_nonneg (pow_nonneg inverse_history_discount_range.1.le _) (bankDepthFrame_pos M j).le)
  have hs := (hbase.mul_left ((inverseBankCap .localInverse:ℝ)/2)).add
    (old_signed_depth_rare_summable M hg)
  apply hs.congr
  intro j
  unfold oldSignedSourceHistoryBudget
  ring

end
end ASDExplicitGamma.Native
