module

public import ASDExplicitGamma.Scalar.OldHessianTrialTopPatchRestriction
public import ASDExplicitGamma.Scalar.OldHessianTrialThirdBill

/-! The cellwise frozen principal is the original global principal pairing. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- Both quarter turns in each genuine local TOP receiver are the
restriction of the same two-load fine patched reciprocal receiver. -/
theorem old_hessian_principal_cell_receiver (Q : TriadicCube 2) (fine : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (U : OldSignedCellIndex Q fine) (i : Fin 2) :
    let R := oldHessianCellTopReciprocal Q U.val (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
      nu sigma hnu hsigma k
    let G := fun j : Fin 2 => fun x => (scalarCoefficientFlux (responseFramePlanarCoefficientField nu sigma k)
      (oldSignedLocalResidual Q fine nu sigma hnu hsigma k (fun _ => (basisVec j,0)) (memLp_const (basisVec j,0))) x).2
    (fun x => planarQuarterTurn (R (matVecMul responsePlanarJ (basisVec i)) x))=ᵐ[normalizedCubeMeasure U.val]
      oldHessianRotatedReceiver G i := by
  intro R G
  filter_upwards [old_hessian_rotated_top_load Q U.val
    (openCubeSet_subset_of_mem_descendantsAtDepth U.property) nu sigma hnu hsigma k i,
    old_hessian_top_patch_restrict Q fine nu sigma hnu hsigma k U (basisVec 0),
    old_hessian_top_patch_restrict Q fine nu sigma hnu hsigma k U (basisVec 1)] with x hx h0 h1
  rw [hx]
  fin_cases i
  · simpa [oldHessianRotatedReceiver,R,G] using congrArg planarQuarterTurn h1.symm
  · simpa [oldHessianRotatedReceiver,R,G] using congrArg (fun v : Vec 2 => -planarQuarterTurn v) h0.symm


/-- The frozen cell principal, after the full original partition, is
exactly the principal already controlled by the sharp half-trace budget. -/
theorem old_hessian_principal_cell_join (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) :
    let u := oldHessianMixedPotential Q coarse nu sigma hnu hsigma k
    oldHessianPrincipalSpatialCross Q coarse nu sigma hnu hsigma k=
      oldSignedCellAverage Q (coarse+1) (fun U => ∑ i : Fin 2,cubeAverage U.val (fun x =>
        vecDot (planarQuarterTurn (oldHessianCellTopReciprocal Q U.val
          (openCubeSet_subset_of_mem_descendantsAtDepth U.property) nu sigma hnu hsigma k
          (matVecMul responsePlanarJ (basisVec i)) x))
          ((diagInterpolant Q (coarse+1) (u i).toH1Function).grad x))) := by
  intro u
  let a := responseFramePlanarCoefficientField nu sigma k
  let G := fun i : Fin 2 => fun x => (scalarCoefficientFlux a
    (oldSignedLocalResidual Q (coarse+1) nu sigma hnu hsigma k (fun _ => (basisVec i,0)) (memLp_const (basisVec i,0))) x).2
  let z := fun i => (diagInterpolant Q (coarse+1) (u i).toH1Function).grad
  have hG (i j : Fin 2) : MemLp (fun x => G i x j) 2 (normalizedCubeMeasure Q) :=
    old_hessian_reciprocal_field_memLp Q nu sigma hnu hsigma k _
      (old_signed_local_residual_memLp Q (coarse+1) nu sigma hnu hsigma k _ _) j
  have hRG := old_hessian_rotated_receiver_memLp Q G hG
  change (∑ i : Fin 2,cubeAverage Q (fun x => vecDot (oldHessianRotatedReceiver G i x) (z i x)))=_
  rw [old_signed_cell_average_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hi := old_hessian_vector_pairing_integrable Q _ _ (hRG i)
    (diagInterpolant Q (coarse+1) (u i).toH1Function).grad_memL2_normalizedCubeMeasure
  rw [old_hessian_cube_average_partition Q (coarse+1) _ hi]
  apply congrArg (oldSignedCellAverage Q (coarse+1))
  funext U
  simp only [cubeAverage_eq_integral_normalizedCubeMeasure]
  apply integral_congr_ae
  filter_upwards [old_hessian_principal_cell_receiver Q (coarse+1) nu sigma hnu hsigma k U i] with x hx
  rw [hx]

end
end ASDExplicitGamma.Scalar
