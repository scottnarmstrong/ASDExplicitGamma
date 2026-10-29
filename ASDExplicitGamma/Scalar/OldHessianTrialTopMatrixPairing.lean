module

public import ASDExplicitGamma.Scalar.OldHessianTrialTopMatrix

/-! The actual TOP matrix action under the physical cell pairing. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational
noncomputable section

/-- The two-basis reconstruction holds for the normalized cell measure too. -/
theorem old_hessian_cell_top_matrix_action_normalized (Q U : TriadicCube 2)
    (hU : openCubeSet U⊆openCubeSet Q) (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (e : Vec 2) :
    (fun x => matVecMul (oldHessianCellTopReciprocalMatrix Q U hU nu sigma hnu hsigma k x) e)=ᵐ[
      normalizedCubeMeasure U] oldHessianCellTopReciprocal Q U hU nu sigma hnu hsigma k e := by
  have hh := old_hessian_cell_top_reciprocal_matrix_action Q U hU nu sigma hnu hsigma k e
  unfold volumeMeasureOn at hh
  rw [←volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] at hh
  exact Measure.ae_smul_measure hh _

/-- Every physical pairing with the actual reciprocal matrix is the
pairing with the actual local TOP minimizer at the same deterministic load. -/
theorem old_hessian_cell_top_matrix_pairing (Q U : TriadicCube 2)
    (hU : openCubeSet U⊆openCubeSet Q) (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (e : Vec 2) (w : Vec 2 → Vec 2) :
    cubeAverage U (fun x => vecDot (w x)
      (matVecMul (oldHessianCellTopReciprocalMatrix Q U hU nu sigma hnu hsigma k x) e))=
    cubeAverage U (fun x => vecDot (w x) (oldHessianCellTopReciprocal Q U hU nu sigma hnu hsigma k e x)) := by
  simp only [cubeAverage_eq_integral_normalizedCubeMeasure]
  apply integral_congr_ae
  filter_upwards [old_hessian_cell_top_matrix_action_normalized Q U hU nu sigma hnu hsigma k e] with x hx
  rw [hx]

end
end ASDExplicitGamma.Scalar
