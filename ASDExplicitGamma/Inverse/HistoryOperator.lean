module

public import ASDExplicitGamma.Inverse.HistoryDefectMeasurable
public import ASDExplicitGamma.Inverse.HistoryBuffer

/-! The source operator history is the actual finite descendant maximum,
followed by its normalized infinite geometric sum in the true running frame. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped ENNReal

noncomputable def bufferOperatorMax (M : ABKModel 2) (n : ℤ) (r : ℕ) :
    Cutoff.CutoffSample 2 → ℝ≥0∞ :=
  historyFiniteMax (descendantsAtDepth (originCube 2 (n-40)) r)
    (fun Q ω => ENNReal.ofReal (historyOperatorDefect M n Q ω))

noncomputable def bufferOperatorHistory (M : ABKModel 2) (n : ℤ)
    (ω : Cutoff.CutoffSample 2) : ℝ≥0∞ :=
  ENNReal.ofReal (1-(3:ℝ)^(-(1/4:ℝ)))*
    ∑' r : ℕ, ENNReal.ofReal ((3:ℝ)^(-(1/4:ℝ)*r))*bufferOperatorMax M n r ω

theorem buffer_operator_max_measurable (M : ABKModel 2) (n : ℤ) (r : ℕ) :
    Measurable (bufferOperatorMax M n r) :=
  history_finite_max_measurable _ _ (fun Q => (history_operator_defect_measurable M n Q).ennreal_ofReal)

theorem buffer_operator_max_le_trace (M : ABKModel 2) (n : ℤ) (r : ℕ)
    (ω : Cutoff.CutoffSample 2) : bufferOperatorMax M n r ω ≤ bufferTraceMax M n r ω := by
  unfold bufferOperatorMax bufferTraceMax historyFiniteMax
  apply Finset.sup_le
  intro Q hQ
  exact (ENNReal.ofReal_le_ofReal (history_operator_defect_le_trace M n Q ω)).trans (Finset.le_sup (f := fun Q => ENNReal.ofReal (historyTrace M n Q ω)) hQ)

theorem buffer_operator_history_measurable (M : ABKModel 2) (n : ℤ) :
    Measurable (bufferOperatorHistory M n) :=
  (Measurable.tsum (fun r => (buffer_operator_max_measurable M n r).const_mul _)).const_mul _

theorem buffer_operator_history_le_trace (M : ABKModel 2) (n : ℤ)
    (ω : Cutoff.CutoffSample 2) : bufferOperatorHistory M n ω ≤ bufferTraceHistory M n ω := by
  exact mul_le_mul_of_nonneg_left (ENNReal.tsum_le_tsum (fun r =>
    mul_le_mul_of_nonneg_left (buffer_operator_max_le_trace M n r ω) (zero_le : (0:ℝ≥0∞) ≤ _)))
      (zero_le : (0:ℝ≥0∞) ≤ _)

/-- The normalized u=1/8 operator history is bounded by the frozen L20 series. -/
theorem buffer_operator_history_L20 (M : ABKModel 2) (n : ℤ) :
    eLpNorm (bufferOperatorHistory M n) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤ buffer40History M n := by
  apply le_trans _ (buffer_trace_history_L20 M n)
  apply eLpNorm_mono_enorm_ae (buffer_operator_history_measurable M n).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ω => by
    simpa only [enorm_eq_self] using buffer_operator_history_le_trace M n ω)

/-- IN-HISTORY-CONVERSION: the state cap supplies the actual normalized random-history bound. -/
theorem buffer_operator_history_L12 (M : ABKModel 2) (n : ℤ)
    (hcap : buffer40History M n ≤ ENNReal.ofReal (61/10*theta M)) :
    eLpNorm (bufferOperatorHistory M n) 12 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (61/10*theta M) :=
  (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (12:ℝ≥0∞) ≤ 20)).trans
    ((buffer_operator_history_L20 M n).trans hcap)

end ASDExplicitGamma.Inverse
