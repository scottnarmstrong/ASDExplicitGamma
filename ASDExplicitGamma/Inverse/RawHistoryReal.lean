module

public import ASDExplicitGamma.Inverse.ClippedMatrixGoodCap

/-! Literal real depth maxima and the finite positive raw-history series. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- Real value of the actual finite maximum at one descendant depth. -/
def rawDefectDepthMax (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2) (r : ℕ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  (historyFiniteMax (descendantsAtDepth Q r) (fun R ω => ENNReal.ofReal (historyOperatorDefect M n R ω)) ω).toReal

/-- This finite maximum is finite on every actual sample. -/
theorem raw_defect_finite_max_ne_top (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2) (r : ℕ)
    (ω : Cutoff.CutoffSample 2) :
    historyFiniteMax (descendantsAtDepth Q r) (fun R ω => ENNReal.ofReal (historyOperatorDefect M n R ω)) ω ≠ ⊤ := by
  apply ne_of_lt
  apply (Finset.sup_lt_iff (by simp : (⊥ : ℝ≥0∞) < ⊤)).mpr
  intro R _
  exact ENNReal.ofReal_lt_top

/-- Every actual descendant's same-frame defect lies below its real depth maximum. -/
theorem operator_defect_le_depth_max (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2) (r : ℕ)
    (ω : Cutoff.CutoffSample 2) {R : TriadicCube 2} (hR : R ∈ descendantsAtDepth Q r) :
    historyOperatorDefect M n R ω ≤ rawDefectDepthMax M n Q r ω := by
  have hh := ENNReal.toReal_mono (raw_defect_finite_max_ne_top M n Q r ω)
    (Finset.le_sup (f := fun R => ENNReal.ofReal (historyOperatorDefect M n R ω)) hR)
  rwa [ENNReal.toReal_ofReal (show 0 ≤ historyOperatorDefect M n R ω from norm_nonneg _)] at hh

/-- The real positive weighted maxima have precisely the real value of the
literal extended raw history, without replacing them by a trace history. -/
theorem raw_history_real_tsum_eq (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) :
    (∑' r : ℕ, (3:ℝ)^(-(1/2:ℝ)*r)*rawDefectDepthMax M n Q r ω)=
      (clippedCellRawHistory M n Q ω).toReal := by
  unfold clippedCellRawHistory
  rw [ENNReal.tsum_toReal_eq (fun r => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (raw_defect_finite_max_ne_top M n Q r ω))]
  apply tsum_congr
  intro r
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity)]
  rfl

/-- Good history proves summability and its real budget before sensitivity. -/
theorem good_raw_history_real_series (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2)
    (τ : ℝ) (hτ : 0 ≤ τ) (ω : Cutoff.CutoffSample 2) (hgood : ω ∈ clippedCellGoodEvent M n Q τ) :
    Summable (fun r : ℕ => (3:ℝ)^(-(1/2:ℝ)*r)*rawDefectDepthMax M n Q r ω) ∧
      (∑' r : ℕ, (3:ℝ)^(-(1/2:ℝ)*r)*rawDefectDepthMax M n Q r ω) ≤ τ := by
  have hfinite : clippedCellRawHistory M n Q ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hgood
  have hs := ENNReal.summable_toReal hfinite
  have he (r : ℕ) :
      (ENNReal.ofReal ((3:ℝ)^(-(1/2:ℝ)*r))*historyFiniteMax (descendantsAtDepth Q r)
        (fun R ω => ENNReal.ofReal (historyOperatorDefect M n R ω)) ω).toReal =
        (3:ℝ)^(-(1/2:ℝ)*r)*rawDefectDepthMax M n Q r ω := by
    rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity)]
    rfl
  refine ⟨by simpa only [clippedCellRawHistory,he] using hs,?_⟩
  rw [raw_history_real_tsum_eq]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hgood).trans_eq (ENNReal.toReal_ofReal hτ)

end
end ASDExplicitGamma.Inverse
