module

public import ASDExplicitGamma.Scalar.AnalyticInverseTrace
public import Mathlib.Data.Finset.Lattice.Fold

/-! The actual largest-eigenvalue parameter in the scalar analytic estimates. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Matrix

/-- The largest eigenvalue of a real Hermitian matrix, without an estimate in its definition. -/
noncomputable def largestHermitianEigenvalue {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty hA.eigenvalues

/-- SC-ANALYTIC-BOUND-M, with the source largest-eigenvalue parameter and trace excess. -/
theorem largest_eigenvalue_le_of_coarse_duality {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A R : Matrix ι ι ℝ) (hA : A.PosDef) (hR : Rᵀ*R=1)
    (hdual : (A-R*A⁻¹*Rᵀ).PosSemidef) :
    let T := A.trace-(Fintype.card ι:ℝ)
    0≤T ∧ largestHermitianEigenvalue A hA.isHermitian≤1+2*T+Real.sqrt (2*T) := by
  have h := eigenvalues_le_of_coarse_duality A R hA hR hdual
  refine ⟨h.1,?_⟩
  exact Finset.sup'_le _ _ (fun i _ => h.2 i)

end ASDExplicitGamma.Scalar
