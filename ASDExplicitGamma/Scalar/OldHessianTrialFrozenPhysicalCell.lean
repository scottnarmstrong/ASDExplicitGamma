module

public import ASDExplicitGamma.Scalar.OldHessianTrialFrozenCellContraction
public import ASDExplicitGamma.Scalar.OldHessianTrialTopMatrixPairing
public import ASDExplicitGamma.Scalar.OldHessianTrialPrincipalContraction

/-! The exact frozen contraction for genuine nodal gradients and local TOP fields. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- The fixed planar matrix is the spatial quarter turn in the source notation. -/
theorem old_hessian_j_action_quarter_turn (v : Vec 2) :
    matVecMul responsePlanarJ v=planarQuarterTurn v := by
  funext i
  fin_cases i <;> simp [matVecMul,responsePlanarJ,planarQuarterTurn,Fin.sum_univ_two]

/-- Frozen cell covariance on the actual fine TOP receiver. Actual H1
regularity, matrix L2 and all white convergence are proved internally. -/
theorem old_hessian_frozen_physical_cell (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (U : OldSignedCellIndex Q (coarse+1)) (lam : ℝ) :
    let u := oldHessianMixedPotential Q coarse nu sigma hnu hsigma k
    let z := fun i => (diagInterpolant Q (coarse+1) (u i).toH1Function).grad
    let R := oldHessianCellTopReciprocal Q U.val (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
      nu sigma hnu hsigma k
    HasSum (fun j : whiteBasisIndex => 2*lam*(∑ i : Fin 2,cubeAverage U.val (fun x =>
      vecDot ((cubeAverage U.val (q3Convolution b L h3Zero (whiteBasis j))) •
        matVecMul responsePlanarJ (z i x))
        (R (oldSignedBlockMean U.val (oldSignedFlatMinusBlock Q b L j i)).1 x))))
      (-lam*b^2*(∑ i : Fin 2,cubeAverage U.val (fun x =>
        vecDot (planarQuarterTurn (R (matVecMul responsePlanarJ (basisVec i)) x)) (z i x)))-
       2*lam*(∑ i : Fin 2,cubeAverage U.val (fun x =>
        vecDot (planarQuarterTurn (R (matVecMul (oldHessianMeanCovarianceError Q U.val b L) (basisVec i)) x)) (z i x)))) := by
  intro u z R
  let T := oldHessianCellTopReciprocalMatrix Q U.val
    (openCubeSet_subset_of_mem_descendantsAtDepth U.property) nu sigma hnu hsigma k
  have hz (i l : Fin 2) : MemLp (fun x => z i x l) 2 (normalizedCubeMeasure U.val) :=
    hilbert_memLp_descendant U.property ((diagInterpolant Q (coarse+1) (u i).toH1Function).grad_memL2_normalizedCubeMeasure l)
  have hT (i j : Fin 2) : MemLp (fun x => T x i j) 2 (normalizedCubeMeasure U.val) :=
    old_hessian_cell_top_reciprocal_memLp Q U.val
      (openCubeSet_subset_of_mem_descendantsAtDepth U.property) nu sigma hnu hsigma k _ i
  have hh := old_hessian_frozen_cell_contraction Q (coarse+1) b L U.val U.property z T hz hT lam
  have hpair (i : Fin 2) (e : Vec 2) : cubeAverage U.val (fun x => vecDot (z i x)
      (matVecMul responsePlanarJ (matVecMul (T x) e)))=
      cubeAverage U.val (fun x => vecDot (planarQuarterTurn (R e x)) (z i x)) := by
    simp only [cubeAverage_eq_integral_normalizedCubeMeasure]
    apply integral_congr_ae
    filter_upwards [old_hessian_cell_top_matrix_action_normalized Q U.val
      (openCubeSet_subset_of_mem_descendantsAtDepth U.property) nu sigma hnu hsigma k e] with x hx
    rw [hx,old_hessian_j_action_quarter_turn,vecDot_comm]
  have hprincipal := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => hpair i (matVecMul responsePlanarJ (basisVec i)))
  have herror := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ =>
    hpair i (matVecMul (oldHessianMeanCovarianceError Q U.val b L) (basisVec i)))
  rw [hprincipal,herror] at hh
  exact hh.congr_fun (fun j => congrArg (fun v : ℝ => 2*lam*v)
    (Finset.sum_congr rfl (fun i _ => (old_hessian_cell_top_matrix_pairing Q U.val
      (openCubeSet_subset_of_mem_descendantsAtDepth U.property) nu sigma hnu hsigma k
      (oldSignedBlockMean U.val (oldSignedFlatMinusBlock Q b L j i)).1
      (fun x => (cubeAverage U.val (q3Convolution b L h3Zero (whiteBasis j))) •
        matVecMul responsePlanarJ (z i x))).symm)))

end
end ASDExplicitGamma.Scalar
