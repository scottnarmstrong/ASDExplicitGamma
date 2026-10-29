module

public import ASDExplicitGamma.Inverse.StoppedHistoryMaxima

/-! The frozen mixed history cap controls every actual translated fine-root history. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- The normalized random trace history on one actual translated fine root. -/
def stoppedCellTraceHistory (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) : ℝ≥0∞ :=
  ENNReal.ofReal (1-(3:ℝ)^(-(1/4:ℝ)))*
    ∑' r : ℕ, ENNReal.ofReal ((3:ℝ)^(-(1/4:ℝ)*r))*stoppedCellTraceMax M n Q r ω

theorem stopped_cell_trace_history_measurable (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2) :
    Measurable (stoppedCellTraceHistory M n Q) :=
  (Measurable.tsum (fun r => (stopped_cell_trace_max_measurable M n Q r).const_mul _)).const_mul _

/-- The exact nine-to-the-depth finite population cost at any translated root. -/
theorem stopped_cell_trace_max_L20 (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2)
    (hQ : Q.scale = n-40) (r : ℕ) :
    eLpNorm (stoppedCellTraceMax M n Q r) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ((9:ℝ≥0∞)^r)^(1/20:ℝ)*
        eLpNorm (cutoffTraceDefect M n (n-40-r)) 20 (Cutoff.cutoffSampleLaw M).toMeasure := by
  let S := descendantsAtDepth Q r
  have hnorm (R : TriadicCube 2) (hR : R ∈ S) :
      eLpNorm (fun ω => ENNReal.ofReal (historyTrace M n R ω)) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
        eLpNorm (cutoffTraceDefect M n (n-40-r)) 20 (Cutoff.cutoffSampleLaw M).toMeasure := by
    rw [history_trace_ofReal_norm]
    have hscale : R.scale = n-40-r := by
      rw [scale_eq_sub_of_mem_descendantsAtDepth hR,hQ]
    rw [hscale]
  have hb := history_finite_max_L20 (Cutoff.cutoffSampleLaw M).toMeasure S
    (fun R ω => ENNReal.ofReal (historyTrace M n R ω))
    (fun R => (history_trace_measurable M n R).ennreal_ofReal) _ hnorm
  have hcard : (S.card:ℝ≥0∞) = (9:ℝ≥0∞)^r := by
    dsimp only [S]
    rw [descendantsAtDepth_card]
    norm_num
  rw [hcard] at hb
  exact hb

/-- The native frozen mixed history budget controls the actual translated
normalized random history, before any raw-history conversion or Markov bound. -/
theorem stopped_cell_trace_history_L20 (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2)
    (hQ : Q.scale = n-40) :
    eLpNorm (stoppedCellTraceHistory M n Q) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤ buffer40History M n := by
  let A := ENNReal.ofReal (1-(3:ℝ)^(-(1/4:ℝ)))
  let w (r : ℕ) := ENNReal.ofReal ((3:ℝ)^(-(1/4:ℝ)*r))
  let F (r : ℕ) (ω : Cutoff.CutoffSample 2) := w r*stoppedCellTraceMax M n Q r ω
  have hF (r : ℕ) : Measurable (F r) := (stopped_cell_trace_max_measurable M n Q r).const_mul (w r)
  change eLpNorm (fun ω => A*∑' r, F r ω) 20 _ ≤ _
  rw [history_constant_mul_L20 _ A _ (Measurable.tsum hF)]
  calc
    _ ≤ A*∑' r, eLpNorm (F r) 20 (Cutoff.cutoffSampleLaw M).toMeasure :=
      mul_le_mul_of_nonneg_left (history_ennreal_tsum_L20 _ F hF) (zero_le : (0:ℝ≥0∞) ≤ A)
    _ = A*∑' r, w r*eLpNorm (stoppedCellTraceMax M n Q r) 20 (Cutoff.cutoffSampleLaw M).toMeasure := by
      congr 1
      apply tsum_congr
      intro r
      exact history_constant_mul_L20 _ (w r) _ (stopped_cell_trace_max_measurable M n Q r)
    _ ≤ A*∑' r, w r*(((9:ℝ≥0∞)^r)^(1/20:ℝ)*
        eLpNorm (cutoffTraceDefect M n (n-40-r)) 20 (Cutoff.cutoffSampleLaw M).toMeasure) :=
      mul_le_mul_of_nonneg_left (ENNReal.tsum_le_tsum (fun r =>
        mul_le_mul_of_nonneg_left (stopped_cell_trace_max_L20 M n Q hQ r) (zero_le : (0:ℝ≥0∞) ≤ w r)))
        (zero_le : (0:ℝ≥0∞) ≤ A)
    _ = buffer40History M n := by
      rw [buffer40_history_eq]
      congr 1
      apply tsum_congr
      intro r
      dsimp only [w]
      rw [← mul_assoc,history_population_weight]

end
end ASDExplicitGamma.Inverse
