module

public import ASDExplicitGamma.Scalar.DropParity
public import ASDExplicitGamma.Scalar.DropNormalization
public import ASDExplicitGamma.Scalar.DropResponse
public import ASDExplicitGamma.Native.OldSignedCoarsePairing

/-! The unit observable of the OLD-Hessian trial equals the open-cube response-frame energy
observable of the parity theorem, on `K = closure (cubeSet Q)` (SC-ONE-SHELL-RECIPROCAL-DROP). -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Algsuperdiff.Section3

noncomputable section

theorem drop_open_energy_eq_coarse (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (P : BlockVec 2) (k : ResponseCoefficient (openCubeSet Q)) :
    responseFrameEnergyObservable (measurableSet_openCubeSet Q)
      (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q) ν σ hν hσ P k =
      blockVecDot P (blockMatVecMul (coarseBlockMatrix (openCubeSet Q)
        (responseFramePlanarCoefficientField ν σ k)) P) := by
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hvol : 0 < (volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q
  have hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q) ν σ hν hσ k
  have hObs : responseFrameEnergyObservable (measurableSet_openCubeSet Q) hvol ν σ hν hσ P k =
      2 * Mu (openCubeSet Q) P (responseFramePlanarCoefficientField ν σ k) := by
    rw [lemmaV_observable_eq_twice_muCandidate]
    rw [← lemmaV_responseSystem_eq_canonical (measurableSet_openCubeSet Q) hvol ν σ hν hσ k]
    have hcan := lemmaV_canonical_muCandidate_eq_Mu (isOpenBoundedConvexDomain_openCubeSet Q)
      hEll hvol P
    exact congrArg (fun z : ℝ => 2 * z) hcan
  obtain ⟨A, S, K, hA, -, -, -, -, -⟩ :=
    Internal.Ch02.BookCh02.exists_oldCanonicalMatrixData_of_isOpenBoundedConvexDomain
      (isOpenBoundedConvexDomain_openCubeSet Q) hEll hvol
  have hq : Mu (openCubeSet Q) P (responseFramePlanarCoefficientField ν σ k) =
      (1 / 2 : ℝ) * blockVecDot P (blockMatVecMul (coarseBlockMatrix (openCubeSet Q)
        (responseFramePlanarCoefficientField ν σ k)) P) := by
    simpa only [eq_coarseBlockMatrix_of_isCoarseBlockMatrix hA] using hA.2 P
  rw [hObs, hq]
  ring

theorem drop_unit_observable_eq_open (n : ℤ) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (e : Vec 2)
    (hQ : closure (openCubeSet (originCube 2 n)) ⊆ closure (cubeSet (originCube 2 n)))
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    oldHessianUnitObservable n ν σ e x =
      responseFrameEnergyObservable (measurableSet_openCubeSet (originCube 2 n))
        (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos _) ν σ hν hσ (0, e)
        (physicalResponseRestriction (originCube 2 n) hQ x) := by
  rw [old_hessian_unit_observable_eq_energy n ν σ hν hσ e x]
  rw [drop_open_energy_eq_coarse (originCube 2 n) ν σ hν hσ (0, e)]
  rw [responseFrameEnergyObservable_eq_frameCoarseQuadratic
    (measurableSet_cubeSet (originCube 2 n)) (volume_cubeSet_toReal_pos (originCube 2 n))
    ν σ hν hσ (0, e)]
  congr 2
  rw [← response_coarseMatrix_frame_eq (measurableSet_cubeSet (originCube 2 n)) ν σ hν hσ,
    coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube (originCube 2 n)]
  apply coarseBlockMatrix_congr_of_ae_eq
  filter_upwards [ae_restrict_mem (measurableSet_openCubeSet (originCube 2 n))] with y hy
  have hyc : y ∈ cubeSet (originCube 2 n) := openCubeSet_subset_cubeSet _ hy
  change responsePlanarCoefficient (ν / σ)
      (responseCoefficientExtension (ContinuousMap.linearIsometryBoundedOfCompact _ ℝ ℝ x) y / σ) =
    responsePlanarCoefficient (ν / σ)
      (responseCoefficientExtension (physicalResponseRestriction (originCube 2 n) hQ x) y / σ)
  rw [responseCoefficientExtension_eq _ hy, responseCoefficientExtension_eq _ hyc]
  rfl

end

end ASDExplicitGamma.Scalar
