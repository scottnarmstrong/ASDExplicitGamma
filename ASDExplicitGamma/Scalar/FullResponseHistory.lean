module

public import ASDExplicitGamma.Scalar.CellResidualMean
public import ASDExplicitGamma.Scalar.InverseHistory

/-! The complete full-response source history, with its exact quarter-power discount. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Response Variational
open scoped ENNReal

/-- The complete depth-j maximum of the actual four-dimensional response norm. -/
noncomputable def fullResponseDepthMax (Q : TriadicCube 2) (a : CoeffField 2) (j : ℕ) : ℝ :=
  Book.Ch02.finsetSupReal (descendantsAtDepth Q j) (fun R => fullResponseOperatorNorm R a)

/-- The source full-response history M_U, retaining every depth including zero. -/
noncomputable def completeFullResponseHistory (Q : TriadicCube 2) (a : CoeffField 2) : ℝ≥0∞ :=
  ENNReal.ofReal (1-inverseHistoryDiscount)*∑' j : ℕ,
    ENNReal.ofReal (inverseHistoryDiscount^j*fullResponseDepthMax Q a j)

/-- Each actual depth maximum is nonnegative. -/
theorem full_response_depth_max_nonneg (Q : TriadicCube 2) (a : CoeffField 2) (j : ℕ) :
    0 ≤ fullResponseDepthMax Q a j :=
  Book.Ch02.finsetSupReal_nonneg _ _ (fun R _ => full_response_operator_norm_nonneg R a)

/-- Every actual descendant norm is below its exact finite maximum. -/
theorem full_response_norm_le_depth_max (Q R : TriadicCube 2) (a : CoeffField 2) (j : ℕ)
    (hR : R ∈ descendantsAtDepth Q j) : fullResponseOperatorNorm R a ≤ fullResponseDepthMax Q a j := by
  unfold fullResponseDepthMax Book.Ch02.finsetSupReal
  exact le_csSup (((Set.toFinite _).image _).bddAbove) ⟨R,hR,rfl⟩

end ASDExplicitGamma.Scalar
