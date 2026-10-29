module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith

/-! The square-symmetry matrix step behind MA-DIRECTIONAL-COVARIANCE. -/

@[expose] public section

namespace ASDExplicitGamma.Main

/-- A symmetric two-dimensional covariance matrix invariant under a quarter
turn is isotropic. A trace bound `ξ` therefore gives the source half-bound in
each coordinate. This isolates the geometric step for the actual expected
directional matrices. -/
theorem main_quarter_turn_covariance_half_bound
    (A : Matrix (Fin 2) (Fin 2) ℝ) (xi : ℝ)
    (hSym : A 0 1 = A 1 0)
    (hDiag : A 0 0 = A 1 1)
    (hQuarter : A 0 1 = -A 1 0)
    (hTrace : Matrix.trace A ≤ xi) :
    A 0 1 = 0 ∧ A 1 0 = 0 ∧ A 0 0 ≤ xi / 2 ∧ A 1 1 ≤ xi / 2 := by
  have hOff : A 0 1 = 0 := by linarith
  have hOtherOff : A 1 0 = 0 := by rw [← hSym]; exact hOff
  have hTrace' : A 0 0 + A 1 1 ≤ xi := by
    simpa only [Matrix.trace_fin_two] using hTrace
  have hHalf : A 0 0 ≤ xi / 2 := by
    rw [← hDiag] at hTrace'
    linarith
  exact ⟨hOff, hOtherOff, hHalf, by simpa [hDiag] using hHalf⟩

end ASDExplicitGamma.Main
