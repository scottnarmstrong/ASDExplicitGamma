module

public import ASDExplicitGamma.Main.PanelComparison
public import ASDExplicitGamma.Main.FrameAlgebra
public import ASDExplicitGamma.Statements.Theta
public import ASDExplicitGamma.Scalar.StructuralContinuity
public import ASDExplicitGamma.Numerics.MainReturnCertificate.RecurrenceFields
public import ASDExplicitGamma.Numerics.Spike.CompositionCommon
public import Mathlib.Tactic.FieldSimp

/-! Deterministic comparison of one analytic panel with its certified return-grid step. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Set MeasureTheory ASDExplicitGamma.Numerics
open ASDExplicitGamma.Numerics.MainReturnCertificate
open ASDExplicitGamma.Numerics.Spike
open Homogenization Algsuperdiff.Section3

/-- The panel data embedded in a MainReturnCertificate endpoint, in the record shape
consumed by the outward integer recurrence. -/
def mainPanelCertOfEndpoints (e : PanelEndpoints) : PanelCert :=
  { aUpper := e.aUpper, ellLower := e.ellLower,
    rhoLower := e.rhoLower, rhoUpper := e.rhoUpper,
    offsetLower := e.offsetLower, offsetUpper := e.offsetUpper,
    supportELower := e.supportELower, supportEUpper := e.supportEUpper,
    supportLambdaLower := e.supportLambdaLower,
    supportLambdaUpper := e.supportLambdaUpper,
    supportJLower := e.supportJLower, supportJUpper := e.supportJUpper }

/-- The integer endpoint produced panel by panel is exactly the fold used by
the corresponding eight-entry endpoint list. -/
theorem main_panel_grid_recurrence_eq_range_fold
    (e : ℕ → PanelEndpoints) (x : ℕ → ℕ)
    (hnext : ∀ j : ℕ, j < 8 → x (j + 1) = advancePanel (x j)
      (mainPanelCertOfEndpoints (e j))) :
    x 8 = (List.range 8).foldl
      (fun value j => advancePanel value (mainPanelCertOfEndpoints (e j))) (x 0) := by
  let step : ℕ → ℕ → ℕ := fun value j =>
    advancePanel value (mainPanelCertOfEndpoints (e j))
  have hfold : ∀ (j : ℕ), j ≤ 8 →
      x j = (List.range j).foldl step (x 0) := by
    intro j hj
    induction j with
    | zero => simp [step]
    | succ j ih =>
        have hj8 : j < 8 := by omega
        calc
          x (j + 1) = advancePanel (x j)
              (mainPanelCertOfEndpoints (e j)) := hnext j hj8
          _ = step ((List.range j).foldl step (x 0)) j := by
              rw [ih (by omega)]
          _ = (List.range (j + 1)).foldl step (x 0) := by
              simp [step, List.range_succ, List.foldl_append]
  simpa [step] using hfold 8 le_rfl

end ASDExplicitGamma.Main

end
