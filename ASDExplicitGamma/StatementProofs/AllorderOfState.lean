module

public import ASDExplicitGamma.AllOrder.EndgameAssembly

/-!
# Proof of `ASDExplicitGamma.allorder_of_state`

The all-order bounds follow from a full native induction state at every scale, by the all-order endgame.
The statement is in `ASDExplicitGamma/Statements/AllorderOfState.lean`; the proof is assembled here, as
`ASDExplicitGamma.StatementProofs.allorder_of_state`, from proved lemmas.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Algsuperdiff.Section3
open Homogenization
open scoped ENNReal

namespace ASDExplicitGamma.StatementProofs

/-- The all-order consequence of a full native state. -/
theorem allorder_of_state {M : ABKModel 2} {h : ℝ} {m : ℤ}
    (hM : PlanarQ3Gaussian M h := by assumption)
    (hγ : M.gamma ≤ gammaZero := by assumption)
    (hstate : ∀ n : ℤ, nativeInductionState M h n := by assumption) :
    AllOrderBounds M m :=
  ASDExplicitGamma.AllOrder.allorder_of_state_of_reset
    ASDExplicitGamma.AllOrder.order_reset_producer
    (M := M) (h := h) (m := m) hM hγ hstate

end ASDExplicitGamma.StatementProofs
