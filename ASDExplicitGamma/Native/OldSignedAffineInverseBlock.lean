module

public import ASDExplicitGamma.Native.OldSignedAffineScalarCarrier
public import ASDExplicitGamma.Native.OldSignedLocalHistoryMoments
public import ASDExplicitGamma.Scalar.InverseHistoryBlocks

/-! The signed affine inverse-block coefficient is paid by the actual local bank. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian Variational Inverse Algsuperdiff.Section3
noncomputable section

/-- The literal source diagonal blocks equal those of the physical OLD
display coefficient on every actual comparison cell. -/
theorem old_signed_actual_normalized_block (M : ABKModel 2) (n : ℤ) (r : ℕ)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) (plus : Bool) :
    parentBoundaryBandNormalizedBlock M n 1 t U plus ω=
      if plus then (coarseBlockMatrix (openCubeSet U) (oldSignedPartialFrameField M n 1 t ω)).upperLeft
      else (coarseBlockMatrix (openCubeSet U) (oldSignedPartialFrameField M n 1 t ω)).lowerRight := by
  rw [←old_signed_single_band_frame]
  simp only [←coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube U,parentBoundaryBandFrameField]
  rw [native_source_band_coarse_matrix_frame M n 1 t ω hU]
  rfl

/-- Every diagonal inverse entry is below the complete inverse history;
the monotonic depth-zero bound supplies the full constant one. -/
theorem old_signed_inverse_block_entry_le_history (U : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet U) a) (i : Fin 2) :
    (coarseBlockMatrix (openCubeSet U) a).lowerRight i i≤oldSignedInverseHistory U a := by
  have hid := inverse_history_lowerRight U a hEll
  rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube] at hid
  rw [←hid]
  have he := (le_abs_self ((sigmaStarInvCoarse (openCubeSet U) a) i i)).trans
    (Book.Ch02.abs_entry_le_matrixOperatorNorm (sigmaStarInvCoarse (openCubeSet U) a) i i)
  have hh := actual_inverse_depth_discount_bound U a hEll 1 (by norm_num) 0
  simp only [pow_zero,one_mul] at hh
  have hzero : lemmaVInverseDepthMax U a 0=Book.Ch02.matrixNorm (sigmaStarInvCoarse (openCubeSet U) a) := by
    simp [lemmaVInverseDepthMax,descendantsAtDepth_zero,Book.Ch02.finsetSupReal]
  rw [hzero] at hh
  exact he.trans hh

/-- The actual affine inverse scalar coefficient has the unchanged local
bank cap, with integrability and history finiteness discharged internally. -/
theorem old_signed_affine_inverse_scalar_le
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l<n,nativeInductionState M h l) (r : ℕ) (hr : r≤5)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ht : 0≤t ∧ t≤1) :
    parentBoundaryBandBlockMean M n 1 t U false≤(3683/2500:ℝ) := by
  have hb := old_signed_actual_local_history_moments M h hM hg n hpast t ht
  have hi := (parent_boundary_band_block_scalar_law M h hM n 1 (by norm_num) r U hU t false).1 0 0
  have hsplit := old_signed_actual_cell_inverse_history_split M h hM hg n hpast r hr U hU t ht
  apply le_trans (integral_mono_ae hi hb.1 ?_) hb.2.1
  filter_upwards [hsplit] with ω hω
  rw [old_signed_actual_normalized_block M n r U hU t ω false]
  have hEll := (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet (originCube 2 n))
    M.nu (Annealed.sigmaBar M n) M.nu_pos (Annealed.sigmaBar_characterization M n).1
    (oldSignedPartialResponseCoefficient n 1 t ω)).mono (measurableSet_openCubeSet U)
      (openCubeSet_subset_of_mem_descendantsAtDepth hU)
  exact (old_signed_inverse_block_entry_le_history U (oldSignedPartialFrameField M n 1 t ω) hEll 0).trans hω.1

end
end ASDExplicitGamma.Native
