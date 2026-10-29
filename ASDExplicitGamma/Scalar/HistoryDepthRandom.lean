module

public import ASDExplicitGamma.Scalar.HistoryDepth

/-! Genuine random descendant histories at arbitrary physical lag. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Inverse
open Algsuperdiff.Section3
open scoped ENNReal

/-- The actual descendant trace maximum in the true running frame. -/
noncomputable def lagTraceMax (M : ABKModel 2) (n ell : ℤ) (j : ℕ) :
    Cutoff.CutoffSample 2 → ℝ≥0∞ :=
  historyFiniteMax (descendantsAtDepth (originCube 2 (n-ell)) j)
    (fun Q ω => ENNReal.ofReal (historyTrace M n Q ω))

/-- The complete normalized random trace history at physical lag ell. -/
noncomputable def lagTraceHistory (M : ABKModel 2) (n ell : ℤ) (ω : Cutoff.CutoffSample 2) : ℝ≥0∞ :=
  ENNReal.ofReal (1-(3:ℝ)^(-(1/4:ℝ)))*
    ∑' j : ℕ,ENNReal.ofReal ((3:ℝ)^(-(1/4:ℝ)*j))*lagTraceMax M n ell j ω

theorem lag_trace_max_measurable (M : ABKModel 2) (n ell : ℤ) (r : ℕ) :
    Measurable (lagTraceMax M n ell r) :=
  history_finite_max_measurable _ _ (fun Q => (history_trace_measurable M n Q).ennreal_ofReal)

/-- Nine-to-the-depth descendants pay exactly the one-twentieth population factor. -/
theorem lag_trace_max_L20 (M : ABKModel 2) (n ell : ℤ) (r : ℕ) :
    eLpNorm (lagTraceMax M n ell r) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ((9:ℝ≥0∞)^r)^(1/20:ℝ)*
        eLpNorm (cutoffTraceDefect M n (n-ell-r)) 20 (Cutoff.cutoffSampleLaw M).toMeasure := by
  let s := descendantsAtDepth (originCube 2 (n-ell)) r
  have hnorm (Q : TriadicCube 2) (hQ : Q ∈ s) :
      eLpNorm (fun ω => ENNReal.ofReal (historyTrace M n Q ω)) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
        eLpNorm (cutoffTraceDefect M n (n-ell-r)) 20 (Cutoff.cutoffSampleLaw M).toMeasure := by
    rw [history_trace_ofReal_norm]
    have hscale : Q.scale = n-ell-r := by
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

/-- The genuine normalized random maximum history is controlled by the frozen L20 series. -/
theorem lag_trace_history_L20 (M : ABKModel 2) (n ell : ℤ) :
    eLpNorm (lagTraceHistory M n ell) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤ traceMomentHistory M n ell := by
  let A := ENNReal.ofReal (1-(3:ℝ)^(-(1/4:ℝ)))
  let w (r : ℕ) := ENNReal.ofReal ((3:ℝ)^(-(1/4:ℝ)*r))
  let F (r : ℕ) (ω : Cutoff.CutoffSample 2) := w r*lagTraceMax M n ell r ω
  have hF (r : ℕ) : Measurable (F r) := (lag_trace_max_measurable M n ell r).const_mul (w r)
  change eLpNorm (fun ω => A*∑' r, F r ω) 20 _ ≤ _
  rw [history_constant_mul_L20 _ A _ (Measurable.tsum hF)]
  calc
    _ ≤ A*∑' r, eLpNorm (F r) 20 (Cutoff.cutoffSampleLaw M).toMeasure :=
      mul_le_mul_of_nonneg_left (history_ennreal_tsum_L20 _ F hF) (zero_le : (0:ℝ≥0∞) ≤ A)
    _ = A*∑' r, w r*eLpNorm (lagTraceMax M n ell r) 20 (Cutoff.cutoffSampleLaw M).toMeasure := by
      congr 1
      apply tsum_congr
      intro r
      exact history_constant_mul_L20 _ (w r) _ (lag_trace_max_measurable M n ell r)
    _ ≤ A*∑' r, w r*(((9:ℝ≥0∞)^r)^(1/20:ℝ)*
        eLpNorm (cutoffTraceDefect M n (n-ell-r)) 20 (Cutoff.cutoffSampleLaw M).toMeasure) := by
      exact mul_le_mul_of_nonneg_left (ENNReal.tsum_le_tsum (fun r =>
        mul_le_mul_of_nonneg_left (lag_trace_max_L20 M n ell r) (zero_le : (0:ℝ≥0∞) ≤ w r)))
        (zero_le : (0:ℝ≥0∞) ≤ A)
    _ = traceMomentHistory M n ell := by
      unfold traceMomentHistory
      congr 1
      apply tsum_congr
      intro r
      dsimp only [w]
      rw [← mul_assoc,history_population_weight]

/-- The required L12 history is supplied by the same complete L20 population budget. -/
theorem lag_trace_history_L12 (M : ABKModel 2) (n ell : ℤ) :
    eLpNorm (lagTraceHistory M n ell) 12 (Cutoff.cutoffSampleLaw M).toMeasure ≤ traceMomentHistory M n ell :=
  (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (12:ℝ≥0∞) ≤ 20)).trans
    (lag_trace_history_L20 M n ell)

/-- The completed state controls the actual depth-14 random history needed by the upper source. -/
theorem upper_depth_fourteen_random_history (M : ABKModel 2) (h : ℝ) (n : ℤ)
    (hstate : nativeInductionState M h n) (hθ : theta M ≤ 1) :
    eLpNorm (lagTraceHistory M n 14) 12 (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (61/10:ℝ) :=
  (lag_trace_history_L12 M n 14).trans
    ((trace_moment_history_fourteen_le_forty M n).trans (upper_depth_fourteen_history M h n hstate hθ).2)

end ASDExplicitGamma.Scalar
