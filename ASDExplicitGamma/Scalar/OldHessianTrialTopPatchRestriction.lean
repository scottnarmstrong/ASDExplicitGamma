module

public import ASDExplicitGamma.Scalar.OldHessianTrialTopMatrixPairing
public import ASDExplicitGamma.Scalar.OldHessianTrialRotatedReceiver
public import ASDExplicitGamma.Native.OldSignedAffineCellResidual

/-! Actual local TOP fields are restrictions of the same fine patched response. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- The physical patched reciprocal column is the actual local TOP
column on every fine cell, with the same completed parent coefficient. -/
theorem old_hessian_top_patch_restrict (Q : TriadicCube 2) (fine : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (U : OldSignedCellIndex Q fine) (e : Vec 2) :
    (fun x => (scalarCoefficientFlux (responseFramePlanarCoefficientField nu sigma k)
      (oldSignedLocalResidual Q fine nu sigma hnu hsigma k (fun _ => (e,0)) (memLp_const (e,0))) x).2)=ᵐ[
      normalizedCubeMeasure U.val]
        oldHessianCellTopReciprocal Q U.val (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
          nu sigma hnu hsigma k e := by
  have hh := old_signed_local_residual_restrict Q fine nu sigma hnu hsigma k
    (fun _ => (e,0)) (memLp_const (e,0)) U.val U.property
  rw [old_signed_affine_cell_residual] at hh
  have he : (fun x => (scalarCoefficientFlux (responseFramePlanarCoefficientField nu sigma k)
      (oldSignedLocalResidual Q fine nu sigma hnu hsigma k (fun _ => (e,0)) (memLp_const (e,0))) x).2)=ᵐ[
      volumeMeasureOn (openCubeSet U.val)]
        oldHessianCellTopReciprocal Q U.val (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
          nu sigma hnu hsigma k e := by
    filter_upwards [hh,old_signed_cell_frame_coefficient_ae Q U.val
      (openCubeSet_subset_of_mem_descendantsAtDepth U.property) nu sigma k] with x hx ha
    unfold oldHessianCellTopReciprocal oldSignedDualReflection
    change (blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField nu sigma k) x)
      (oldSignedLocalResidual Q fine nu sigma hnu hsigma k (fun _ => (e,0)) (memLp_const (e,0)) x)).2=_
    rw [hx]
    simp only [scalarCoefficientFlux,blockCoeffField,←ha]
    rfl
  unfold volumeMeasureOn at he
  rw [←volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] at he
  exact Measure.ae_smul_measure he _

/-- The source's load quarter turn is precisely the actual two-column
rotated TOP receiver, with no independent representative choice. -/
theorem old_hessian_rotated_top_load (Q U : TriadicCube 2)
    (hU : openCubeSet U⊆openCubeSet Q) (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (i : Fin 2) :
    (fun x => planarQuarterTurn (oldHessianCellTopReciprocal Q U hU nu sigma hnu hsigma k
      (matVecMul responsePlanarJ (basisVec i)) x))=ᵐ[normalizedCubeMeasure U]
      oldHessianRotatedReceiver (fun j => oldHessianCellTopReciprocal Q U hU nu sigma hnu hsigma k (basisVec j)) i := by
  filter_upwards [old_hessian_cell_top_matrix_action_normalized Q U hU nu sigma hnu hsigma k
    (matVecMul responsePlanarJ (basisVec i))] with x hx
  rw [←hx]
  funext l
  fin_cases i <;> fin_cases l <;>
    simp [oldHessianRotatedReceiver,oldHessianCellTopReciprocalMatrix,matVecMul,
      responsePlanarJ,basisVec,planarQuarterTurn,Fin.sum_univ_two]

/-- Normalized integrability suffices for the actual complete cell partition. -/
theorem old_hessian_cube_average_partition (Q : TriadicCube 2) (fine : ℕ)
    (f : Vec 2 → ℝ) (hf : Integrable f (normalizedCubeMeasure Q)) :
    cubeAverage Q f=oldSignedCellAverage Q fine (fun U => cubeAverage U.val f) := by
  have h0 : ENNReal.ofReal ((cubeVolume Q)⁻¹)≠0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (inv_pos.mpr (cubeVolume_pos Q)))
  have hi : IntegrableOn f (cubeSet Q) volume := (integrable_smul_measure h0 ENNReal.ofReal_ne_top).mp hf
  rw [old_signed_cell_average_eq_descendantsAverage Q fine (fun U => cubeAverage U f)]
  exact cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q fine f hi

end
end ASDExplicitGamma.Scalar
