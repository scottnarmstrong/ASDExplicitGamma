module

public import ASDExplicitGamma.Inverse.HistoryTrace
public import ASDExplicitGamma.Inverse.HistoryMonotoneLp
public import ASDExplicitGamma.Statements.NativeInductionState

/-! The actual buffer-40 trace maximum and normalized history, in sigmaBar M n. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped ENNReal

noncomputable def bufferTraceMax (M : ABKModel 2) (n : ℤ) (r : ℕ) :
    Cutoff.CutoffSample 2 → ℝ≥0∞ :=
  historyFiniteMax (descendantsAtDepth (originCube 2 (n-40)) r)
    (fun Q ω => ENNReal.ofReal (historyTrace M n Q ω))

noncomputable def bufferTraceHistory (M : ABKModel 2) (n : ℤ) (ω : Cutoff.CutoffSample 2) : ℝ≥0∞ :=
  ENNReal.ofReal (1-(3:ℝ)^(-(1/4:ℝ)))*
    ∑' r : ℕ, ENNReal.ofReal ((3:ℝ)^(-(1/4:ℝ)*r))*bufferTraceMax M n r ω

/-- The identity of the frozen coordinate, without any state cap. -/
theorem buffer40_history_eq (M : ABKModel 2) (n : ℤ) :
    buffer40History M n = ENNReal.ofReal (1-(3:ℝ)^(-(1/4:ℝ)))*
      ∑' r : ℕ, ENNReal.ofReal ((3:ℝ)^(-(3/20:ℝ)*r))*
        eLpNorm (cutoffTraceDefect M n (n-40-r)) 20 (Cutoff.cutoffSampleLaw M).toMeasure := rfl

theorem buffer_trace_max_measurable (M : ABKModel 2) (n : ℤ) (r : ℕ) :
    Measurable (bufferTraceMax M n r) :=
  history_finite_max_measurable _ _ (fun Q => (history_trace_measurable M n Q).ennreal_ofReal)

/-- Nine-to-the-depth descendants pay exactly the one-twentieth population factor. -/
theorem buffer_trace_max_L20 (M : ABKModel 2) (n : ℤ) (r : ℕ) :
    eLpNorm (bufferTraceMax M n r) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ((9:ℝ≥0∞)^r)^(1/20:ℝ)*
        eLpNorm (cutoffTraceDefect M n (n-40-r)) 20 (Cutoff.cutoffSampleLaw M).toMeasure := by
  let s := descendantsAtDepth (originCube 2 (n-40)) r
  have hnorm (Q : TriadicCube 2) (hQ : Q ∈ s) :
      eLpNorm (fun ω => ENNReal.ofReal (historyTrace M n Q ω)) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
        eLpNorm (cutoffTraceDefect M n (n-40-r)) 20 (Cutoff.cutoffSampleLaw M).toMeasure := by
    rw [history_trace_ofReal_norm]
    have hscale : Q.scale = n-40-r := by
      simpa only [originCube] using scale_eq_sub_of_mem_descendantsAtDepth hQ
    rw [hscale]
  have hb := history_finite_max_L20 (Cutoff.cutoffSampleLaw M).toMeasure s
    (fun Q ω => ENNReal.ofReal (historyTrace M n Q ω))
    (fun Q => (history_trace_measurable M n Q).ennreal_ofReal) _ hnorm
  have hcard : (s.card : ℝ≥0∞) = (9:ℝ≥0∞)^r := by
    dsimp only [s]
    rw [descendantsAtDepth_card]
    norm_num
  rw [hcard] at hb
  exact hb

/-- Exact cancellation of the quarter discount against the L20 population payment. -/
theorem history_population_weight (r : ℕ) :
    ENNReal.ofReal ((3:ℝ)^(-(1/4:ℝ)*r))*((9:ℝ≥0∞)^r)^(1/20:ℝ) =
      ENNReal.ofReal ((3:ℝ)^(-(3/20:ℝ)*r)) := by
  rw [← ENNReal.ofReal_rpow_of_pos (by norm_num : (0:ℝ) < 3),
    ← ENNReal.ofReal_rpow_of_pos (by norm_num : (0:ℝ) < 3)]
  norm_num only [ENNReal.ofReal_ofNat]
  have h9 : (9:ℝ≥0∞) = (3:ℝ≥0∞)^(2:ℝ) := by norm_num
  rw [h9,← ENNReal.rpow_natCast,← ENNReal.rpow_mul,← ENNReal.rpow_mul,
    ← ENNReal.rpow_add _ _ (by norm_num : (3:ℝ≥0∞) ≠ 0) (by norm_num : (3:ℝ≥0∞) ≠ ⊤)]
  congr 1
  ring

/-- The genuine normalized random maximum history is controlled by the frozen L20 series. -/
theorem buffer_trace_history_L20 (M : ABKModel 2) (n : ℤ) :
    eLpNorm (bufferTraceHistory M n) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤ buffer40History M n := by
  let A := ENNReal.ofReal (1-(3:ℝ)^(-(1/4:ℝ)))
  let w (r : ℕ) := ENNReal.ofReal ((3:ℝ)^(-(1/4:ℝ)*r))
  let F (r : ℕ) (ω : Cutoff.CutoffSample 2) := w r*bufferTraceMax M n r ω
  have hF (r : ℕ) : Measurable (F r) := (buffer_trace_max_measurable M n r).const_mul (w r)
  change eLpNorm (fun ω => A*∑' r, F r ω) 20 _ ≤ _
  rw [history_constant_mul_L20 _ A _ (Measurable.tsum hF)]
  calc
    _ ≤ A*∑' r, eLpNorm (F r) 20 (Cutoff.cutoffSampleLaw M).toMeasure :=
      mul_le_mul_of_nonneg_left (history_ennreal_tsum_L20 _ F hF) (zero_le : (0:ℝ≥0∞) ≤ A)
    _ = A*∑' r, w r*eLpNorm (bufferTraceMax M n r) 20 (Cutoff.cutoffSampleLaw M).toMeasure := by
      congr 1
      apply tsum_congr
      intro r
      exact history_constant_mul_L20 _ (w r) _ (buffer_trace_max_measurable M n r)
    _ ≤ A*∑' r, w r*(((9:ℝ≥0∞)^r)^(1/20:ℝ)*
        eLpNorm (cutoffTraceDefect M n (n-40-r)) 20 (Cutoff.cutoffSampleLaw M).toMeasure) := by
      exact mul_le_mul_of_nonneg_left (ENNReal.tsum_le_tsum (fun r =>
        mul_le_mul_of_nonneg_left (buffer_trace_max_L20 M n r) (zero_le : (0:ℝ≥0∞) ≤ w r)))
        (zero_le : (0:ℝ≥0∞) ≤ A)
    _ = buffer40History M n := by
      rw [buffer40_history_eq]
      congr 1
      apply tsum_congr
      intro r
      dsimp only [w]
      rw [← mul_assoc,history_population_weight]

end ASDExplicitGamma.Inverse
