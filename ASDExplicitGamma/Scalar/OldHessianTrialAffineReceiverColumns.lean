module

public import ASDExplicitGamma.Scalar.OldHessianTrialTopReceiverField
public import ASDExplicitGamma.Scalar.OldHessianTrialMinusMeanBank

/-! Original minus affine receiver columns before physical labels are frozen. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- Genuine reciprocal local TOP column at an original finite-parent minus mean. -/
def oldHessianMinusAffineSpatialColumn (Q : TriadicCube 2) (fine : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (p : whiteBasisIndex×Fin 2) (U : OldSignedCellIndex Q fine) : Vec 2 → Vec 2 :=
  oldHessianCellTopReciprocal Q U.val (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
    nu sigma hnu hsigma k (oldHessianMinusMeanColumn Q fine b L p U)

/-- The original local reciprocal receiver's full spatial weak energy. -/
def oldHessianMinusAffineSpatialEnergy (Q : TriadicCube 2) (fine : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (p : whiteBasisIndex×Fin 2) : ℝ :=
  oldSignedCellAverage Q fine (fun U => vectorWeakHaarEnergy U.val
    (oldHessianMinusAffineSpatialColumn Q fine nu sigma hnu hsigma k b L p U))

theorem old_hessian_minus_affine_spatial_column_memLp (Q : TriadicCube 2) (fine : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (p : whiteBasisIndex×Fin 2) (U : OldSignedCellIndex Q fine) (i : Fin 2) :
    MemLp (fun x => oldHessianMinusAffineSpatialColumn Q fine nu sigma hnu hsigma k b L p U x i)
      2 (normalizedCubeMeasure U.val) :=
  old_hessian_cell_top_reciprocal_memLp Q U.val
    (openCubeSet_subset_of_mem_descendantsAtDepth U.property) nu sigma hnu hsigma k _ i

end
end ASDExplicitGamma.Scalar
