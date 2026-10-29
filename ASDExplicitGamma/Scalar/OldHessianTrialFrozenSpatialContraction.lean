module

public import ASDExplicitGamma.Scalar.OldHessianTrialFrozenPhysicalCell
public import ASDExplicitGamma.Scalar.OldHessianTrialPrincipalCellJoin
public import ASDExplicitGamma.Scalar.OldHessianTrialCovarianceSpatial
public import ASDExplicitGamma.Native.OldSignedSpatialSeriesBound

/-! Full signed frozen covariance with the original spatial principal and error. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- One complete two-load source/TOP mode, on the unchanged fine cells. -/
def oldHessianFrozenSpatialTerm (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (lam : ℝ) (j : whiteBasisIndex) : ℝ :=
  let u := oldHessianMixedPotential Q coarse nu sigma hnu hsigma k
  oldSignedCellAverage Q (coarse+1) (fun U => 2*lam*(∑ i : Fin 2,cubeAverage U.val (fun x =>
    vecDot ((cubeAverage U.val (q3Convolution b L h3Zero (whiteBasis j))) •
      matVecMul responsePlanarJ ((diagInterpolant Q (coarse+1) (u i).toH1Function).grad x))
      (oldHessianCellTopReciprocal Q U.val (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
        nu sigma hnu hsigma k (oldSignedBlockMean U.val (oldSignedFlatMinusBlock Q b L j i)).1 x))))

/-- The complete signed source covariance has exactly its negative
principal and finite-parent error. All cell, load and mode interchanges and
physical receiver identifications have been proved, not assumed. -/
theorem old_hessian_frozen_spatial_contraction (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l}) (lam : ℝ) :
    HasSum (oldHessianFrozenSpatialTerm Q coarse nu sigma hnu hsigma k b L lam)
      (-lam*b^2*oldHessianPrincipalSpatialCross Q coarse nu sigma hnu hsigma k-
        2*lam*oldHessianCovarianceSpatialCross Q coarse nu sigma hnu hsigma k b L) := by
  let u := oldHessianMixedPotential Q coarse nu sigma hnu hsigma k
  let z := fun i => (diagInterpolant Q (coarse+1) (u i).toH1Function).grad
  let R := fun U : OldSignedCellIndex Q (coarse+1) => oldHessianCellTopReciprocal Q U.val
    (openCubeSet_subset_of_mem_descendantsAtDepth U.property) nu sigma hnu hsigma k
  let f := fun (j : whiteBasisIndex) (U : OldSignedCellIndex Q (coarse+1)) =>
    2*lam*(∑ i : Fin 2,cubeAverage U.val (fun x =>
      vecDot ((cubeAverage U.val (q3Convolution b L h3Zero (whiteBasis j))) •
        matVecMul responsePlanarJ (z i x))
        (R U (oldSignedBlockMean U.val (oldSignedFlatMinusBlock Q b L j i)).1 x)))
  let p := fun U : OldSignedCellIndex Q (coarse+1) => ∑ i : Fin 2,cubeAverage U.val (fun x =>
    vecDot (planarQuarterTurn (R U (matVecMul responsePlanarJ (basisVec i)) x)) (z i x))
  let c := fun U : OldSignedCellIndex Q (coarse+1) => ∑ i : Fin 2,cubeAverage U.val (fun x =>
    vecDot (planarQuarterTurn (R U (matVecMul (oldHessianMeanCovarianceError Q U.val b L) (basisVec i)) x)) (z i x))
  have hs (U : OldSignedCellIndex Q (coarse+1)) : HasSum (fun j => f j U) (-lam*b^2*p U-2*lam*c U) :=
    old_hessian_frozen_physical_cell Q coarse nu sigma hnu hsigma k b L U lam
  have hh := old_signed_cell_average_series Q (coarse+1) f (fun U => (hs U).summable)
  have he : (∑' j,oldSignedCellAverage Q (coarse+1) (f j))=
      -lam*b^2*oldHessianPrincipalSpatialCross Q coarse nu sigma hnu hsigma k-
        2*lam*oldHessianCovarianceSpatialCross Q coarse nu sigma hnu hsigma k b L := by
    rw [hh.2]
    simp_rw [fun U => (hs U).tsum_eq]
    rw [old_signed_cell_average_sub,old_signed_cell_average_mul,old_signed_cell_average_mul]
    rw [←old_hessian_principal_cell_join Q coarse nu sigma hnu hsigma k]
    rfl
  rw [←he]
  exact hh.1.hasSum

end
end ASDExplicitGamma.Scalar
