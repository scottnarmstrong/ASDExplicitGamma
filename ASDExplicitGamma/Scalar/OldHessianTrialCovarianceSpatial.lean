module

public import ASDExplicitGamma.Scalar.OldHessianTrialTopReceiverField
public import ASDExplicitGamma.Scalar.OldHessianTrialNodalBrokenPairing
public import ASDExplicitGamma.Scalar.OldHessianTrialPrincipalContraction

/-! The spatial covariance identity is proved before physical depth substitution. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- One actual cell-dependent covariance receiver column at arbitrary depth. -/
def oldHessianCovarianceSpatialReceiver (Q : TriadicCube 2) (fine : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l}) (i : Fin 2) : ℝ :=
  oldSignedCellAverage Q fine (fun U => vectorWeakHaarEnergy U.val
    (oldHessianCellTopReciprocal Q U.val (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
      nu sigma hnu hsigma k (matVecMul (oldHessianMeanCovarianceError Q U.val b L) (basisVec i))))

/-- Genuine two-load covariance-error cross, with the original fine I. -/
def oldHessianCovarianceSpatialCross (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l}) : ℝ :=
  let u := oldHessianMixedPotential Q coarse nu sigma hnu hsigma k
  oldSignedCellAverage Q (coarse+1) (fun U => ∑ i : Fin 2,cubeAverage U.val (fun x =>
    vecDot (planarQuarterTurn (oldHessianCellTopReciprocal Q U.val
      (openCubeSet_subset_of_mem_descendantsAtDepth U.property) nu sigma hnu hsigma k
      (matVecMul (oldHessianMeanCovarianceError Q U.val b L) (basisVec i)) x))
      ((diagInterpolant Q (coarse+1) (u i).toH1Function).grad x)))

/-- The actual spatial cross pays the complete mixed-gradient weak energy
and actual local reciprocal receiver energy, with constant one. -/
theorem old_hessian_covariance_spatial_pairing (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l}) :
    |oldHessianCovarianceSpatialCross Q coarse nu sigma hnu hsigma k b L|≤
      Real.sqrt (∑ i : Fin 2,lemmaVTiledWeakEnergy Q (coarse+1)
        (oldHessianMixedPotential Q coarse nu sigma hnu hsigma k i).toH1Function.grad)*
      Real.sqrt (∑ i : Fin 2,oldHessianCovarianceSpatialReceiver Q (coarse+1) nu sigma hnu hsigma k b L i) := by
  let u := oldHessianMixedPotential Q coarse nu sigma hnu hsigma k
  let G := fun (U : OldSignedCellIndex Q (coarse+1)) (i : Fin 2) (x : Vec 2) =>
    planarQuarterTurn (oldHessianCellTopReciprocal Q U.val
      (openCubeSet_subset_of_mem_descendantsAtDepth U.property) nu sigma hnu hsigma k
      (matVecMul (oldHessianMeanCovarianceError Q U.val b L) (basisVec i)) x)
  have hG (U : OldSignedCellIndex Q (coarse+1)) (i l : Fin 2) :
      MemLp (fun x => G U i x l) 2 (normalizedCubeMeasure U.val) :=
    old_hessian_cell_top_reciprocal_rotate_memLp Q U.val
      (openCubeSet_subset_of_mem_descendantsAtDepth U.property) nu sigma hnu hsigma k _ l
  have hh := old_hessian_nodal_broken_pairing Q (coarse+1) u G hG
  have hR : (∑ i : Fin 2,oldSignedCellAverage Q (coarse+1) (fun U => vectorWeakHaarEnergy U.val (G U i)))=
      ∑ i : Fin 2,oldHessianCovarianceSpatialReceiver Q (coarse+1) nu sigma hnu hsigma k b L i := by
    dsimp only [G]
    simp_rw [old_hessian_weak_energy_quarter_turn]
    rfl
  rw [hR] at hh
  exact hh

end
end ASDExplicitGamma.Scalar
