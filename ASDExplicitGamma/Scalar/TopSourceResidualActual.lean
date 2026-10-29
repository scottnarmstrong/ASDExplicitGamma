module

public import ASDExplicitGamma.Scalar.TopSourceResidual
public import Homogenization.CoarseGraining.CoarseBounds.AeBridge

/-! Exact coefficient and descendant-history identification for the actual OLD cutoff. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
noncomputable section
open Homogenization Response Variational MeasureTheory Triadic
open Algsuperdiff.Section3

/-- The literal normalized OLD cutoff coefficient on the physical square. -/
def oldCutoffNormalizedCoefficient (M : ABKModel 2) (n : ℤ)
    (ω : Cutoff.CutoffSample 2) : CoeffField 2 :=
  fun x => (Annealed.sigmaBar M n : ℝ)⁻¹ • Cutoff.coefficientCutoff M.nu n ω x

/-- The response frame coefficient is pointwise the actual OLD coefficient divided by sigmaBar. -/
theorem old_cutoff_frame_coefficient_eq_normalized (M : ABKModel 2) (n : ℤ)
    (Q : TriadicCube 2) (ω : Cutoff.CutoffSample 2) {x : Vec 2}
    (hx : x ∈ openCubeSet Q) :
    responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n : ℝ)
        (oldCutoffSkewCoefficient n Q ω) x = oldCutoffNormalizedCoefficient M n ω x := by
  rw [responseFramePlanarCoefficientField_apply,
    old_cutoff_skew_coefficient_value n Q ω hx]
  unfold oldCutoffNormalizedCoefficient
  rw [← old_cutoff_coefficient_planar]
  rw [responsePlanarCoefficient]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply,Matrix.add_apply,smul_eq_mul,responsePlanarJ,responsePlanarCoefficient] <;> ring

/-- Every descendant's actual coarse matrix, hence its full response norm, agrees with the frame realization. -/
theorem old_cutoff_full_response_norm_eq (M : ABKModel 2) (n : ℤ)
    (Q R : TriadicCube 2) (ω : Cutoff.CutoffSample 2) (j : ℕ)
    (hR : R ∈ descendantsAtDepth Q j) :
    fullResponseOperatorNorm R
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n : ℝ)
        (oldCutoffSkewCoefficient n Q ω)) =
    fullResponseOperatorNorm R (oldCutoffNormalizedCoefficient M n ω) := by
  have hsub : openCubeSet R ⊆ openCubeSet Q :=
    openCubeSet_subset_of_mem_descendantsAtDepth hR
  have hae : responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n : ℝ)
      (oldCutoffSkewCoefficient n Q ω) =ᵐ[volume.restrict (openCubeSet R)]
      oldCutoffNormalizedCoefficient M n ω := by
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet R)] with x hx
    exact old_cutoff_frame_coefficient_eq_normalized M n Q ω (hsub hx)
  have hmatrix := coarseBlockMatrix_congr_of_ae_eq hae
  unfold fullResponseOperatorNorm
  rw [Variational.cube_coarseMatrix_eq_open R
    (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n : ℝ)
      (oldCutoffSkewCoefficient n Q ω)),
    Variational.cube_coarseMatrix_eq_open R (oldCutoffNormalizedCoefficient M n ω),hmatrix]

/-- The equality of full-response depth maxima is valid at every depth. -/
theorem old_cutoff_full_response_depth_max_eq (M : ABKModel 2) (n : ℤ)
    (Q : TriadicCube 2) (ω : Cutoff.CutoffSample 2) (j : ℕ) :
    fullResponseDepthMax Q
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n : ℝ)
        (oldCutoffSkewCoefficient n Q ω)) j =
    fullResponseDepthMax Q (oldCutoffNormalizedCoefficient M n ω) j := by
  apply Book.Ch02.finsetSupReal_congr
  intro R hR
  exact old_cutoff_full_response_norm_eq M n Q R ω j hR

/-- The full source history is exactly the complete history of the actual normalized OLD coefficient. -/
theorem old_cutoff_complete_history_eq (M : ABKModel 2) (n : ℤ)
    (Q : TriadicCube 2) (ω : Cutoff.CutoffSample 2) :
    completeFullResponseHistory Q
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n : ℝ)
        (oldCutoffSkewCoefficient n Q ω)) =
    completeFullResponseHistory Q (oldCutoffNormalizedCoefficient M n ω) := by
  unfold completeFullResponseHistory
  apply congrArg (fun z => ENNReal.ofReal (1-inverseHistoryDiscount) * z)
  apply tsum_congr
  intro j
  rw [old_cutoff_full_response_depth_max_eq M n Q ω j]

/-- SC-LAMBDA8-TOP-SOURCE-RESIDUAL with the literal normalized OLD coefficient history. -/
theorem old_cutoff_top_source_residual_actual (M : ABKModel 2) (n : ℤ)
    (Q : TriadicCube 2) (ω : Cutoff.CutoffSample 2)
    (f : Vec 2 → Vec 2) (hf : ScalarPositiveHaarAdmissible Q f) :
    ENNReal.ofReal (cubeAverage Q (fun x => blockVecDot
      (scalarResidualField Q M.nu (Annealed.sigmaBar M n : ℝ)
        M.nu_pos (Annealed.sigmaBar M n).property
        (oldCutoffSkewCoefficient n Q ω)
        (toHilbertBlockL2OfBlockField (scalar_source_block_memL2 Q hf.memLp)) x)
      (scalarCoefficientFlux
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n : ℝ)
          (oldCutoffSkewCoefficient n Q ω))
        (scalarResidualField Q M.nu (Annealed.sigmaBar M n : ℝ)
          M.nu_pos (Annealed.sigmaBar M n).property
          (oldCutoffSkewCoefficient n Q ω)
          (toHilbertBlockL2OfBlockField (scalar_source_block_memL2 Q hf.memLp))) x))) ≤
    completeFullResponseHistory Q (oldCutoffNormalizedCoefficient M n ω) *
      ENNReal.ofReal (positiveSourceEnergy Q f) := by
  rw [← old_cutoff_complete_history_eq M n Q ω]
  exact old_cutoff_top_source_residual M n Q ω f hf

end
end ASDExplicitGamma.Scalar
