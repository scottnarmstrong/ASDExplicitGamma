module

public import ASDExplicitGamma.Scalar.ProjectionCharacterization
public import ASDExplicitGamma.Variational.LemmaVMinimizer
public import ASDExplicitGamma.Variational.AdapterMu
public import ASDExplicitGamma.Variational.CubeOpen

/-! Actual affine response tests on every cell, with exact coarse-matrix energy. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Response Variational MeasureTheory

/-- Every source observation square has finite physical volume. -/
instance instScalarSquareFiniteVolume (Q : TriadicCube 2) : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- The canonical concrete doubled operator system on a source cell. -/
noncomputable def scalarCellSystem (Q : TriadicCube 2) (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) : MuOperatorSystemData (openCubeSet Q) a :=
  (PotentialSolenoidalL2Data.ofSubmoduleClosures (openCubeSet Q)).toMuOperatorSystemDataOfIsEllipticFieldOn
    hEll (by rw [volume_openCubeSet_toReal];exact cubeVolume_pos Q)

/-- The actual recovered affine minimizer test, using the existing Sobolev recovery theorem. -/
noncomputable def scalarCellResponseTest (Q : TriadicCube 2) (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (P : BlockVec 2) : BlockState 2 := by
  letI finiteScalarTestConstruction : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  exact (lemmaVRecoveryData (isOpenBoundedConvexDomain_openCubeSet Q)).toMuCorrectionSpaceRecoveryData.recoveredField
    (scalarCellSystem Q a hEll) P

/-- The cell test has genuine L2 fields. -/
theorem scalar_cell_response_test_memL2 (Q : TriadicCube 2) (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (P : BlockVec 2) :
    MemBlockL2 (openCubeSet Q) (scalarCellResponseTest Q a hEll P).eval := by
  let finiteScalarTestL2 : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  exact (lemmaVRecoveryData (isOpenBoundedConvexDomain_openCubeSet Q)).toMuCorrectionSpaceRecoveryData.recoveredField_memBlockL2
    (scalarCellSystem Q a hEll) P

/-- Its correction is an actual zero-trace/zero-normal-trace source variation. -/
theorem scalar_cell_response_test_variation (Q : TriadicCube 2) (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (P : BlockVec 2) :
    ScalarVariation (openCubeSet Q) (fun x => (scalarCellResponseTest Q a hEll P).eval x-P) := by
  letI finiteScalarCellResponseVolume : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have h := (lemmaVRecoveryData (isOpenBoundedConvexDomain_openCubeSet Q)).toMuCorrectionSpaceRecoveryData.recoveredField_admissible
    (scalarCellSystem Q a hEll) P
  refine ⟨(scalar_cell_response_test_memL2 Q a hEll P).sub (memLp_const P),?_,?_⟩
  · convert h.isPotentialZeroTrace using 1 <;> rfl
  · convert h.isSolenoidalZeroNormalTrace using 1 <;> rfl

/-- The cell test energy is exactly the physical full coarse response quadratic form. -/
theorem scalar_cell_response_test_energy (Q : TriadicCube 2) (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (P : BlockVec 2) :
    volumeAverage (openCubeSet Q) (fun x => blockVecDot ((scalarCellResponseTest Q a hEll P).eval x)
      (blockMatVecMul (blockCoeffField a x) ((scalarCellResponseTest Q a hEll P).eval x)))=
      blockVecDot P (blockMatVecMul (coarseBlockMatrix (cubeSet Q) a) P) := by
  letI finiteScalarCellTestVolume : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  let R := (lemmaVRecoveryData (isOpenBoundedConvexDomain_openCubeSet Q)).toMuCorrectionSpaceRecoveryData
  let M := scalarCellSystem Q a hEll
  have hE := R.blockEnergyAverage_affineField_correctionPart_eq_muCandidate M P
  rw [R.affineField_correctionPart] at hE
  change blockEnergyAverage (openCubeSet Q) a (R.recoveredField M P)=M.toMuHilbertRealization.muCandidate P at hE
  have hmu := lemmaV_canonical_muCandidate_eq_Mu (isOpenBoundedConvexDomain_openCubeSet Q) hEll
    (show 0 < (volume (openCubeSet Q)).toReal by rw [volume_openCubeSet_toReal];exact cubeVolume_pos Q) P
  change M.toMuHilbertRealization.muCandidate P=Mu (openCubeSet Q) P a at hmu
  rw [hmu] at hE
  obtain ⟨A,S,K,hA,_,_,_,_,_⟩ := Internal.Ch02.BookCh02.exists_oldCanonicalMatrixData_of_isOpenBoundedConvexDomain
    (isOpenBoundedConvexDomain_openCubeSet Q) hEll
    (show 0 < (volume (openCubeSet Q)).toReal by rw [volume_openCubeSet_toReal];exact cubeVolume_pos Q)
  have hquad := hA.2 P
  rw [eq_coarseBlockMatrix_of_isCoarseBlockMatrix hA] at hquad
  rw [cube_coarseMatrix_eq_open]
  unfold blockEnergyAverage at hE
  change volumeAverage (openCubeSet Q) ((1/2:ℝ) • (fun x => blockVecDot
    ((R.recoveredField M P).eval x) (blockMatVecMul (blockCoeffField a x) ((R.recoveredField M P).eval x))))=
      Mu (openCubeSet Q) P a at hE
  rw [volumeAverage_smul] at hE
  change (1/2:ℝ)*volumeAverage (openCubeSet Q) (fun x =>
    blockVecDot ((scalarCellResponseTest Q a hEll P).eval x)
      (blockMatVecMul (blockCoeffField a x) ((scalarCellResponseTest Q a hEll P).eval x)))=
        Mu (openCubeSet Q) P a at hE
  linarith only [hE,hquad]

end ASDExplicitGamma.Scalar
