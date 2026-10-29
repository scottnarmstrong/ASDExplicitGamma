module

public import ASDExplicitGamma.Scalar.AnalyticBound
public import Homogenization.Ambient.BlockMatrix

/-! The four-dimensional source block swap and analytic scalar bound. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Matrix

/-- The source orthogonal block-swap involution R. -/
def scalarBlockSwap : FullBlockMat 2 := Matrix.fromBlocks 0 1 1 0

/-- R is symmetric, so its orthogonal congruence is the source R A inverse R. -/
theorem scalarBlockSwap_transpose : scalarBlockSwapᵀ=scalarBlockSwap := by
  simp [scalarBlockSwap,Matrix.fromBlocks_transpose]

/-- The block swap is orthogonal without an additional premise. -/
theorem scalarBlockSwap_orthogonal : scalarBlockSwapᵀ*scalarBlockSwap=1 := by
  rw [scalarBlockSwap_transpose]
  simp [scalarBlockSwap,Matrix.fromBlocks_multiply,← Matrix.fromBlocks_one]

/-- SC-ANALYTIC-BOUND-M in the literal source dimension and block convention. -/
theorem scalar_analytic_bound (A : FullBlockMat 2) (hA : A.PosDef)
    (hdual : (A-scalarBlockSwap*A⁻¹*scalarBlockSwap).PosSemidef) :
    let T := A.trace-4
    0≤T ∧ largestHermitianEigenvalue A hA.isHermitian≤1+2*T+Real.sqrt (2*T) := by
  have hd : (A-scalarBlockSwap*A⁻¹*scalarBlockSwapᵀ).PosSemidef := by
    rwa [scalarBlockSwap_transpose]
  simpa only [Fintype.card_sum,Fintype.card_fin,show (2+2:ℕ)=4 by rfl,Nat.cast_ofNat] using
    largest_eigenvalue_le_of_coarse_duality A scalarBlockSwap hA scalarBlockSwap_orthogonal hd

end ASDExplicitGamma.Scalar
