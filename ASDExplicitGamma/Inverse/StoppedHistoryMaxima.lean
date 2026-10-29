module

public import ASDExplicitGamma.Inverse.HistoryTraceMonotone
public import ASDExplicitGamma.Inverse.ClippedMatrixEvent

/-! Arbitrary translated-root trace maxima for the actual local old-history marks. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- The actual finite trace maximum, for any translated fine root. -/
def stoppedCellTraceMaxReal (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2) (r : ℕ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  (descendantsAtDepth Q r).sup' (descendantsAtDepth_nonempty Q r) (fun R => historyTrace M n R ω)

def stoppedCellTraceMax (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2) (r : ℕ) :
    Cutoff.CutoffSample 2 → ℝ≥0∞ :=
  historyFiniteMax (descendantsAtDepth Q r) (fun R ω => ENNReal.ofReal (historyTrace M n R ω))

/-- The two literal finite maximum conventions agree. -/
theorem stopped_cell_trace_max_real_eq (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2) (r : ℕ)
    (ω : Cutoff.CutoffSample 2) :
    ENNReal.ofReal (stoppedCellTraceMaxReal M n Q r ω) = stoppedCellTraceMax M n Q r ω := by
  unfold stoppedCellTraceMaxReal stoppedCellTraceMax historyFiniteMax
  apply le_antisymm
  · obtain ⟨R,hR,he⟩ := Finset.exists_mem_eq_sup' (descendantsAtDepth_nonempty Q r) (fun R => historyTrace M n R ω)
    rw [he]
    exact Finset.le_sup (f := fun R => ENNReal.ofReal (historyTrace M n R ω)) hR
  · apply Finset.sup_le
    intro R hR
    convert ENNReal.ofReal_le_ofReal (Finset.le_sup' (fun R => historyTrace M n R ω) hR) using 1

/-- Coarse subadditivity gives monotonicity at the actual translated root,
not just the origin-cube representative used by the frozen history norm. -/
theorem stopped_cell_trace_max_real_monotone (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) : Monotone (fun r => stoppedCellTraceMaxReal M n Q r ω) := by
  apply monotone_nat_of_le_succ
  intro r
  change (descendantsAtDepth Q r).sup' _ _ ≤ _
  apply Finset.sup'_le
  intro R hR
  calc
    historyTrace M n R ω ≤ descendantsAverage R 1 (fun S => historyTrace M n S ω) := history_trace_subadditive M n R 1 ω
    _ ≤ descendantsAverage R 1 (fun _ => stoppedCellTraceMaxReal M n Q (r+1) ω) := by
      apply descendantsAverage_le_descendantsAverage
      intro S hS
      unfold stoppedCellTraceMaxReal
      have hmem : S ∈ descendantsAtDepth Q (r+1) :=
        mem_descendantsAtDepth_succ_iff.mpr ⟨R,hR,by simpa only [descendantsAtDepth_one] using hS⟩
      convert Finset.le_sup' (fun S => historyTrace M n S ω) hmem using 1
    _ = stoppedCellTraceMaxReal M n Q (r+1) ω := descendantsAverage_const _ _ _

theorem stopped_cell_trace_max_monotone (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) : Monotone (fun r => stoppedCellTraceMax M n Q r ω) := by
  intro i j hij
  change stoppedCellTraceMax M n Q i ω ≤ stoppedCellTraceMax M n Q j ω
  rw [← stopped_cell_trace_max_real_eq,← stopped_cell_trace_max_real_eq]
  exact ENNReal.ofReal_le_ofReal (stopped_cell_trace_max_real_monotone M n Q ω hij)

theorem stopped_cell_trace_max_measurable (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2) (r : ℕ) :
    Measurable (stoppedCellTraceMax M n Q r) :=
  history_finite_max_measurable _ _ (fun R => (history_trace_measurable M n R).ennreal_ofReal)

end
end ASDExplicitGamma.Inverse
