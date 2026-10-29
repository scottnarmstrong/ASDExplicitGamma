module

public import ASDExplicitGamma.Scalar.TrueFrameNormalization
public import ASDExplicitGamma.Variational.CubeOpen
public import Homogenization.CoarseGraining.MagicIdentities.MuOrdering.HarmonicMean

/-! SC-RECIPROCAL-MOLECULAR-CAP: the constant flux bound is valid at every
completed label, in the physical frame, hence in particular at molecular entrance. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Homogenization.Book MeasureTheory Algsuperdiff.Section3

/-- Pathwise pure-flux competitor, with the actual constant molecular symmetric part. -/
theorem cutoff_physical_inverse_le (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) (e : Vec 2) :
    vecDot e (matVecMul (Homogenization.coarseBlockMatrix (cubeSet Q)
      (Cutoff.coefficientCutoff M.nu m ω).toFun).lowerRight e) ≤ M.nu⁻¹*vecDot e e := by
  rw [Variational.cube_coarseMatrix_eq_open]
  have hConv := isOpenBoundedConvexDomain_openCubeSet Q
  have instFiniteInverseCube : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    hConv.isFiniteMeasure_restrict_volume
  have hvol : 0 < (volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  have hEll := Cutoff.isEllipticFieldOn_coefficientCutoff_cube M m ω Q
  obtain ⟨R,sigma,compat,hA,_,_,_,_,_⟩ :=
    Internal.Ch02.BookCh02.exists_oldCanonicalMatrixData_of_isOpenBoundedConvexDomain hConv hEll hvol
  have h := sigmaStarInvCoarse_le_averaged_symmPart_inv_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    R hConv hEll hvol compat e
  rw [← coarseBlockMatrix_lowerRight_eq_of_isCoarseBlockMatrix hA] at h
  have hi : (M.nu • (1 : Mat 2))⁻¹ = M.nu⁻¹ • (1 : Mat 2) := by
    rw [nonsing_inv_smul M.nu M.nu_pos.ne' (by simp),inv_one]
  have hid (x : Vec 2) : matVecMul (1 : Mat 2) x = x := Matrix.one_mulVec x
  simp_rw [Cutoff.symmPart_coefficientCutoff M.nu m ω,hi,smul_matVecMul,hid,vecDot_smul_right] at h
  rw [volumeAverage_const hvol.ne'] at h
  exact h

/-- The physical inverse response has the constant-flux bound after taking expectation. -/
theorem physicalInverseResponse_le_inv_nu (M : ABKModel 2) (m : ℤ)
    (Q : TriadicCube 2) (e : Vec 2) (he : vecDot e e = 1) :
    physicalInverseResponse M m Q e ≤ M.nu⁻¹ := by
  obtain ⟨s,t,hst⟩ :=
    Provider.Annealed.coefficientCutoffLaw_exists_annealedBlockMatrixAtScale_eq_blockDiag_smul_one M m Q.scale
  have ht : t ≤ M.nu⁻¹ := by
    have hInt := Provider.Annealed.coefficientCutoffLaw_integrable_blockMatEntry_coarseBlockMatrix
      M m Q (Sum.inr 0) (Sum.inr 0)
    change Integrable (fun a : RegCoeffField 2 =>
      (Homogenization.coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight 0 0)
      (Cutoff.coefficientCutoffLaw M m) at hInt
    have hmean : t = ∫ a : RegCoeffField 2,
        (Homogenization.coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight 0 0
        ∂(Cutoff.coefficientCutoffLaw M m) := by
      have hm := Model.annealedBlockMatrix_cube_eq_origin M m Q
      rw [hst] at hm
      have hentry := congrArg (fun A : BlockMat 2 => A.lowerRight 0 0) hm
      simpa only [Ch04.annealedBlockMatrix,Ch02.blockDiag,Matrix.smul_apply,Matrix.one_apply,ite_true,smul_eq_mul,mul_one] using hentry.symm
    rw [Cutoff.coefficientCutoffLaw_eq_map] at hInt hmean
    rw [hmean,integral_map (Cutoff.measurable_coefficientCutoff M.nu m).aemeasurable hInt.aestronglyMeasurable]
    have hSample := (integrable_map_measure hInt.aestronglyMeasurable
      (Cutoff.measurable_coefficientCutoff M.nu m).aemeasurable).mp hInt
    calc
      _ ≤ ∫ _ω, M.nu⁻¹ ∂(Cutoff.cutoffSampleLaw M).toMeasure :=
        integral_mono_ae hSample (integrable_const _) (Filter.Eventually.of_forall (fun ω => by
          simpa [vecDot,matVecMul,Pi.single_apply] using
            cutoff_physical_inverse_le M m Q ω (Pi.single (0 : Fin 2) 1)))
      _ = M.nu⁻¹ := by simp
  unfold physicalInverseResponse
  rw [Model.annealedBlockMatrix_cube_eq_origin,hst]
  have hid : matVecMul (1 : Mat 2) e = e := Matrix.one_mulVec e
  simpa only [Ch02.blockDiag,smul_matVecMul,hid,vecDot_smul_right,he,mul_one] using ht

end ASDExplicitGamma.Scalar
