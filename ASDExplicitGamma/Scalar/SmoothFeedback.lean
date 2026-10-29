module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! A planar rotation algebra lemma for the directional Gram step in
SC-SMOOTH-FEEDBACK-GAP. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Matrix

/-- The quarter turn used for the directional averaging in two dimensions. -/
def quarterTurn : Matrix (Fin 2) (Fin 2) ℝ := !![0,-1;1,0]

/-- A symmetric quadratic form invariant under a quarter turn is isotropic.
This is the finite-dimensional algebra behind the factor `1/2` for an
annealed directional Gram. -/
theorem quarter_turn_symmetric_form_isotropic
    (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hsymm : A.transpose = A)
    (hrot : quarterTurn.transpose * A * quarterTurn = A) :
    ∀ e : Fin 2 → ℝ,
      ∑ i : Fin 2, e i * (A.mulVec e) i =
        ((A 0 0 + A 1 1) / 2) * (e 0 ^ 2 + e 1 ^ 2) := by
  have h00 : A 0 0 = A 1 1 := by
    have h := congrFun (congrFun hrot 0) 0
    simp [quarterTurn, Matrix.mul_apply, Fin.sum_univ_two] at h
    linarith
  have h01 : A 0 1 = 0 := by
    have hsym : A 0 1 = A 1 0 := by
      have h := congrFun (congrFun hsymm 0) 1
      simpa using h.symm
    have h := congrFun (congrFun hrot 0) 1
    simp [quarterTurn, Matrix.mul_apply, Fin.sum_univ_two] at h
    linarith
  have h10 : A 1 0 = 0 := by
    have h := congrFun (congrFun hsymm 0) 1
    simpa [h01] using h
  intro e
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [h01, h10]
  rw [h00]
  ring

end ASDExplicitGamma.Scalar
