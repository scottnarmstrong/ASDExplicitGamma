module

public import ASDExplicitGamma.Scalar.HistoryCellMonotonicity

/-! The complete mixed trace history at every buffer depth, in the true running frame. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Inverse
open Algsuperdiff.Section3
open scoped ENNReal

/-- The complete normalized L20 population history at physical buffer lag ell. -/
noncomputable def traceMomentHistory (M : ABKModel 2) (n ell : ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal (1-(3:ℝ)^(-(1/4:ℝ)))*∑' j : ℕ,
    ENNReal.ofReal ((3:ℝ)^(-(3/20:ℝ)*j))*
      eLpNorm (cutoffTraceDefect M n (n-ell-(j:ℤ))) 20 (Cutoff.cutoffSampleLaw M).toMeasure

/-- At lag forty this is the literal frozen induction coordinate. -/
theorem trace_moment_history_forty (M : ABKModel 2) (n : ℤ) :
    traceMomentHistory M n 40=buffer40History M n := rfl

/-- Complete histories increase with buffer depth, including every descendant depth. -/
theorem trace_moment_history_monotone (M : ABKModel 2) (n : ℤ) :
    Monotone (traceMomentHistory M n) := by
  intro a b hab
  apply mul_le_mul_of_nonneg_left _ (zero_le : (0:ℝ≥0∞) ≤ _)
  apply ENNReal.tsum_le_tsum
  intro j
  apply mul_le_mul_of_nonneg_left _ (zero_le : (0:ℝ≥0∞) ≤ _)
  apply trace_cell_L20_antitone M n
  omega

/-- The depth-fourteen source history is controlled by the frozen buffer-forty history. -/
theorem trace_moment_history_fourteen_le_forty (M : ABKModel 2) (n : ℤ) :
    traceMomentHistory M n 14 ≤ buffer40History M n :=
  (trace_moment_history_monotone M n (by norm_num : (14:ℤ) ≤ 40)).trans_eq
    (trace_moment_history_forty M n)

/-- The source history cap alone supplies the absolute depth-fourteen bound. -/
theorem upper_depth_fourteen_history_of_buffer_cap (M : ABKModel 2) (n : ℤ)
    (hcap : buffer40History M n ≤ ENNReal.ofReal (61/10*theta M)) (hθ : theta M ≤ 1) :
    traceMomentHistory M n 14 ≤ buffer40History M n ∧ buffer40History M n ≤ ENNReal.ofReal (61/10:ℝ) := by
  refine ⟨trace_moment_history_fourteen_le_forty M n,?_⟩
  exact hcap.trans (ENNReal.ofReal_le_ofReal (by nlinarith only [hθ]))

/-- The source completed state gives the absolute history cap 6.1. -/
theorem upper_depth_fourteen_history (M : ABKModel 2) (h : ℝ) (n : ℤ)
    (hstate : nativeInductionState M h n) (hθ : theta M ≤ 1) :
    traceMomentHistory M n 14 ≤ buffer40History M n ∧ buffer40History M n ≤ ENNReal.ofReal (61/10:ℝ) := by
  exact upper_depth_fourteen_history_of_buffer_cap M n hstate.2.2.2.1 hθ

end ASDExplicitGamma.Scalar
