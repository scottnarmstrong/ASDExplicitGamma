module

public import ASDExplicitGamma.Scalar.CutoffProjection
public import ASDExplicitGamma.Scalar.CellEnergyCauchy
public import Mathlib.Analysis.Real.Sqrt

/-! Exact principal/residual splitting of the actual weighted cell solve.
These deterministic identities precede the UPPER stochastic estimates. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Response
noncomputable section

/-- Split the true weighted cell solve into the affine and fluctuating loads.
The caller may take P to be the constant cell mean of F. -/
theorem upper_cell_projection_split
    (Q : TriadicCube 2) (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (F P : HilbertBlockL2 (openCubeSet Q)) :
    scalarProjectionResidual Q nu sigma hnu hsigma k F =
      scalarProjectionResidual Q nu sigma hnu hsigma k P +
      scalarProjectionResidual Q nu sigma hnu hsigma k (F-P) := by
  simp only [scalarProjectionResidual_eq_affineMinimizer, map_sub]
  abel

/-- The complete doubled cell energy has the exact principal, cross and
residual terms, retaining the actual coefficient-dependent projection. -/
theorem upper_cell_projection_energy_split
    (Q : TriadicCube 2) (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (F P : HilbertBlockL2 (openCubeSet Q)) :
    let B := (scalarFrameRealization Q nu sigma hnu hsigma k).energyBilin
    let S := scalarProjectionResidual Q nu sigma hnu hsigma k P
    let Y := scalarProjectionResidual Q nu sigma hnu hsigma k (F-P)
    B (scalarProjectionResidual Q nu sigma hnu hsigma k F)
      (scalarProjectionResidual Q nu sigma hnu hsigma k F) =
        B S S+2*B S Y+B Y Y := by
  dsimp only
  rw [upper_cell_projection_split Q nu sigma hnu hsigma k F P]
  simp only [map_add, add_apply]
  rw [(scalarFrameRealization Q nu sigma hnu hsigma k).energySymm
    (scalarProjectionResidual Q nu sigma hnu hsigma k (F-P))
    (scalarProjectionResidual Q nu sigma hnu hsigma k P)]
  ring

/-- Genuine cell-energy Cauchy controls the cross term without independence
or an assumed Cauchy estimate. -/
theorem upper_cell_projection_energy_le
    (Q : TriadicCube 2) (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (F P : HilbertBlockL2 (openCubeSet Q)) :
    let B := (scalarFrameRealization Q nu sigma hnu hsigma k).energyBilin
    let S := scalarProjectionResidual Q nu sigma hnu hsigma k P
    let Y := scalarProjectionResidual Q nu sigma hnu hsigma k (F-P)
    B (scalarProjectionResidual Q nu sigma hnu hsigma k F)
      (scalarProjectionResidual Q nu sigma hnu hsigma k F) ≤
        B S S+2*Real.sqrt (B S S*B Y Y)+B Y Y := by
  dsimp only
  rw [upper_cell_projection_energy_split Q nu sigma hnu hsigma k F P]
  have hc := Real.le_sqrt_of_sq_le (scalar_realized_energy_cauchy
    (scalarFrameRealization Q nu sigma hnu hsigma k)
    (scalarProjectionResidual Q nu sigma hnu hsigma k P)
    (scalarProjectionResidual Q nu sigma hnu hsigma k (F-P)))
  linarith only [hc]

end
end ASDExplicitGamma.Scalar
