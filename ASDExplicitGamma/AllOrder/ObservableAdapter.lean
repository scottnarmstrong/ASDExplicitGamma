module

public import ASDExplicitGamma.Model.Translation
public import ASDExplicitGamma.Scalar.AmplitudeNormalization
public import ASDExplicitGamma.Variational.AdapterMu
public import ASDExplicitGamma.Variational.AdapterDuality
public import ASDExplicitGamma.Variational.TraceDefect
public import Homogenization.Book.Ch02.Theorems.HomogenizationError.EllipticityControl
public import Homogenization.Book.Ch02.Theorems.HomogenizationError.Finite
public import Homogenization.Book.Ch02.Theorems.DeterministicIdentities
public import Algsuperdiff.Section3.Observable.CutoffHomogenizationError

/-! # The cutoff homogenization observable and the trace-defect depth sum -/

@[expose] public section

open MeasureTheory
open Homogenization Homogenization.Book
open Algsuperdiff.Section3
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace ASDExplicitGamma.AllOrder

private noncomputable def observableFrameMatrix (Q : TriadicCube 2)
    (a : CoeffField 2) (sigma : ℝ) : FullBlockMat 2 :=
  toFullBlockMat (Variational.frameMatrix sigma (coarseBlockMatrix (cubeSet Q) a))

private noncomputable def observableDefectMatrix (Q : TriadicCube 2)
    (a : CoeffField 2) (sigma : ℝ) : FullBlockMat 2 :=
  (1 / 2 : ℝ) •
      (observableFrameMatrix Q a sigma +
        Ch04.fullBlockReflect (observableFrameMatrix Q a sigma)) - 1

private theorem frameMatrix_symmetric_adapter (sigma : ℝ) (A : BlockMat 2)
    (hA : IsSymmetricBlockMat A) :
    IsSymmetricBlockMat (Variational.frameMatrix sigma A) := by
  intro α β
  cases α with
  | inl i =>
    cases β with
    | inl j =>
      simpa only [Variational.frameMatrix, blockMatEntry, Matrix.smul_apply,
        smul_eq_mul] using congrArg (fun x : ℝ => sigma⁻¹ * x)
          (hA (Sum.inl i) (Sum.inl j))
    | inr j => exact hA (Sum.inl i) (Sum.inr j)
  | inr i =>
    cases β with
    | inl j => exact hA (Sum.inr i) (Sum.inl j)
    | inr j =>
      simpa only [Variational.frameMatrix, blockMatEntry, Matrix.smul_apply,
        smul_eq_mul] using congrArg (fun x : ℝ => sigma * x)
          (hA (Sum.inr i) (Sum.inr j))

private theorem observableDefectMatrix_isSymm (Q : TriadicCube 2)
    (a : CoeffField 2) (sigma : ℝ) :
    (observableDefectMatrix Q a sigma).IsSymm := by
  let A := coarseBlockMatrix (cubeSet Q) a
  let F := Variational.frameMatrix sigma A
  have hA : IsSymmetricBlockMat A := Variational.coarseBlockMatrix_symmetric _ _
  have hF : IsSymmetricBlockMat F := by
    simpa [F, A] using frameMatrix_symmetric_adapter sigma A hA
  have hM : (toFullBlockMat F).IsSymm := by
    simpa using isSymm_toFullBlockMat_of_isSymmetricBlockMat hF
  have hR : (Ch04.fullBlockReflect (toFullBlockMat F)).IsSymm := by
    rw [Ch04.fullBlockReflect_toFullBlockMat]
    exact isSymm_toFullBlockMat_of_isSymmetricBlockMat
      (isSymmetricBlockMat_blockReflect hF)
  simpa [observableDefectMatrix, observableFrameMatrix, F, A] using
    ((hM.add hR).smul (1 / 2 : ℝ)).sub Matrix.isSymm_one

private theorem traceDefect_eq_frameTrace_cube (Q : TriadicCube 2)
    (a : CoeffField 2) (sigma : ℝ) :
    traceDefect (cubeSet Q) a sigma =
      Matrix.trace (observableFrameMatrix Q a sigma) - 4 := by
  change sigma⁻¹ * Matrix.trace (coarseBlockMatrix (cubeSet Q) a).upperLeft +
      sigma * Matrix.trace (coarseBlockMatrix (cubeSet Q) a).lowerRight - 4 =
    Matrix.trace (toFullBlockMat
      (Variational.frameMatrix sigma (coarseBlockMatrix (cubeSet Q) a))) - 4
  simp [Matrix.trace, toFullBlockMat, Variational.frameMatrix,
    Fintype.sum_sum_type]
  ring

private theorem observableDefectMatrix_trace (Q : TriadicCube 2)
    (a : CoeffField 2) (sigma : ℝ) :
    Matrix.trace (observableDefectMatrix Q a sigma) =
      traceDefect (cubeSet Q) a sigma := by
  have hR : Matrix.trace (Ch04.fullBlockReflect (observableFrameMatrix Q a sigma)) =
      Matrix.trace (observableFrameMatrix Q a sigma) := by
    change Matrix.trace (Ch04.fullBlockReflect (toFullBlockMat
      (Variational.frameMatrix sigma (coarseBlockMatrix (cubeSet Q) a)))) = _
    rw [Ch04.fullBlockReflect_toFullBlockMat]
    simp [observableFrameMatrix, toFullBlockMat,
      Matrix.trace, Fintype.sum_sum_type, blockReflect]
    ring
  unfold observableDefectMatrix
  simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_add]
  rw [hR, traceDefect_eq_frameTrace_cube]
  have hOne : Matrix.trace (1 : FullBlockMat 2) = 4 := by
    simp [Matrix.trace]
  rw [hOne]
  ring

private theorem blockJ_quadratic_eq_defect (A : BlockMat 2)
    (e : FullBlockVec 2) :
    Ch04.blockJQuadraticFullBlockMat (toFullBlockMat A)
        (ofFullBlockVec e) (ofFullBlockVec e) =
      dotProduct e (Matrix.mulVec
        ((1 / 2 : ℝ) • (toFullBlockMat A +
          Ch04.fullBlockReflect (toFullBlockMat A)) - 1) e) := by
  rw [Ch04.blockJQuadraticFullBlockMat, Ch04.fullBlockReflect_toFullBlockMat]
  simp only [Ch04.fullBlockQuadraticCh04, toFullBlockVec_ofFullBlockVec]
  have hdot : blockVecDot (ofFullBlockVec e) (ofFullBlockVec e) = dotProduct e e := by
    simp [blockVecDot, vecDot, ofFullBlockVec, dotProduct, Fintype.sum_sum_type]
  rw [hdot]
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.add_mulVec,
    Matrix.one_mulVec]
  rw [dotProduct_sub, dotProduct_smul, dotProduct_add]
  ring

private noncomputable def observableMatrixNorm (A : FullBlockMat 2) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖

private theorem observableMatrixNorm_le_trace (A : FullBlockMat 2)
    (hA : A.PosSemidef) : observableMatrixNorm A ≤ Matrix.trace A := by
  classical
  let hHerm : A.IsHermitian := hA.isHermitian
  have heig_nonneg : ∀ i : BlockCoord 2, 0 ≤ hHerm.eigenvalues i :=
    hA.eigenvalues_nonneg
  have hsum_nonneg : 0 ≤ ∑ i : BlockCoord 2, hHerm.eigenvalues i :=
    Finset.sum_nonneg fun i _ => heig_nonneg i
  let D : FullBlockMat 2 := Matrix.diagonal hHerm.eigenvalues
  have hspectral : A = Unitary.conjStarAlgAut ℝ _ hHerm.eigenvectorUnitary D := by
    simpa [D] using hHerm.spectral_theorem
  calc
    observableMatrixNorm A = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ := rfl
    _ = ‖A‖ := Matrix.l2_opNorm_toEuclideanCLM A
    _ = ‖Unitary.conjStarAlgAut ℝ _ hHerm.eigenvectorUnitary D‖ :=
      congrArg (fun N : FullBlockMat 2 => ‖N‖) hspectral
    _ = ‖D‖ := by
      calc
        ‖Unitary.conjStarAlgAut ℝ _ hHerm.eigenvectorUnitary D‖ =
            ‖(hHerm.eigenvectorUnitary : FullBlockMat 2) * D *
              star (hHerm.eigenvectorUnitary : FullBlockMat 2)‖ := by
                simp [Unitary.conjStarAlgAut_apply]
        _ = ‖D * star (hHerm.eigenvectorUnitary : FullBlockMat 2)‖ := by
              rw [mul_assoc, CStarRing.norm_coe_unitary_mul]
        _ = ‖D * (star hHerm.eigenvectorUnitary : unitary (FullBlockMat 2))‖ := by simp
        _ = ‖D‖ := by rw [CStarRing.norm_mul_coe_unitary]
    _ = ‖hHerm.eigenvalues‖ := by simp [D]
    _ ≤ ∑ i : BlockCoord 2, hHerm.eigenvalues i := by
      refine (pi_norm_le_iff_of_nonneg hsum_nonneg).mpr ?_
      intro i
      calc
        ‖hHerm.eigenvalues i‖ = hHerm.eigenvalues i := by
          simp [Real.norm_eq_abs, abs_of_nonneg (heig_nonneg i)]
        _ ≤ ∑ j : BlockCoord 2, hHerm.eigenvalues j :=
          Finset.single_le_sum (fun j _ => heig_nonneg j) (Finset.mem_univ i)
    _ = Matrix.trace A := by
      symm
      simpa using hHerm.trace_eq_sum_eigenvalues

private theorem cutoff_frame_quadratic_identity (M : ABKModel 2) (m : ℤ)
    (omega : Cutoff.CutoffSample 2) (Q : TriadicCube 2) (e : FullBlockVec 2) :
    Ch02.doubledResponseJ (Ch02.cubeDomain Q)
        (Cutoff.coefficientCutoffTriadicCoeffFamily M m omega |>.coeffOn Q)
        (ofFullBlockVec (Matrix.mulVec
          (Ch02.constantFullBlockMatrixInvSqrt
            (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m))) e))
        (ofFullBlockVec (Matrix.mulVec
          (Ch02.constantFullBlockMatrixSqrt
            (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m))) e)) =
      dotProduct e (Matrix.mulVec
        (observableDefectMatrix Q (Cutoff.coefficientCutoff M.nu m omega).toFun
          (Annealed.sigmaBar M m : ℝ)) e) := by
  let sigma : ℝ := Annealed.sigmaBar M m
  let a : RegCoeffField 2 := Cutoff.coefficientCutoff M.nu m omega
  let F : Ch02.TriadicCoeffFamily 2 :=
    Cutoff.coefficientCutoffTriadicCoeffFamily M m omega
  have hlocal : Ch04.AELocallyUniformlyEllipticField a := by
    exact Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M m omega
  let G : Ch02.TriadicCoeffFamily 2 :=
    Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a hlocal
  have hFG : Ch02.TriadicCoeffFamily.AEEq F G := by
    intro R
    change (F.coeffOn R).toCoeffField =ᵐ[
      volumeMeasureOn (Ch02.cubeDomain R : Set (Vec 2))]
        (G.coeffOn R).toCoeffField
    simp [F, G, a, Cutoff.coefficientCutoffTriadicCoeffFamily,
      Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField,
      Cutoff.coefficientCutoffCoeffOn]
  let a0 : Mat 2 := Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)
  let A : BlockMat 2 := coarseBlockMatrix (cubeSet Q) a.toFun
  let P : BlockVec 2 := ofFullBlockVec
    (Matrix.mulVec (Ch02.constantFullBlockMatrixInvSqrt a0) e)
  let Pstar : BlockVec 2 := ofFullBlockVec
    (Matrix.mulVec (Ch02.constantFullBlockMatrixSqrt a0) e)
  have ha0 : a0 = scalarMatrix (d := 2) sigma := by
    ext i j
    simp [a0, sigma, Observable.isotropicComparatorMatrix, scalarMatrix]
  have hresponse :
      Ch02.doubledResponseJ (Ch02.cubeDomain Q) (F.coeffOn Q) P Pstar =
        Ch04.blockJQuadraticFullBlockMat (toFullBlockMat A) P Pstar := by
    calc
      _ = Ch02.doubledResponseJ (Ch02.cubeDomain Q) (G.coeffOn Q) P Pstar :=
        Ch02.doubledResponseJ_eq_ofAEEq (hFG Q) P Pstar
      _ = Ch04.blockJObservableCubeSetBlockVec Q P Pstar a :=
        Ch04.doubledResponseJ_eq_blockJObservableCubeSetBlockVec_of_aelocallyUniformlyEllipticField
          hlocal Q P Pstar
      _ = Ch04.blockJQuadraticFullBlockMat (toFullBlockMat A) P Pstar :=
        Ch04.blockJObservableCubeSetBlockVec_eq_blockJQuadraticFullBlockMat_of_aelocallyUniformlyEllipticField
          hlocal Q P Pstar
  have hσ : 0 < sigma := by
    exact (Annealed.sigmaBar M m).property
  have hframe :
      Ch04.blockJQuadraticFullBlockMat (toFullBlockMat A) P Pstar =
        Ch04.blockJQuadraticFullBlockMat
          (toFullBlockMat (Variational.frameMatrix sigma A))
          (ofFullBlockVec e) (ofFullBlockVec e) := by
    simpa [P, Pstar, A, a, a0, sigma, ha0] using
      Scalar.normalized_block_quadratic_eq_frame
        (coarseBlockMatrix (cubeSet Q) a.toFun) sigma hσ e
  calc
    _ = Ch04.blockJQuadraticFullBlockMat (toFullBlockMat A) P Pstar := hresponse
    _ = Ch04.blockJQuadraticFullBlockMat
        (toFullBlockMat (Variational.frameMatrix sigma A))
        (ofFullBlockVec e) (ofFullBlockVec e) := hframe
    _ = dotProduct e (Matrix.mulVec
        (observableDefectMatrix Q a.toFun sigma) e) := by
      simpa [observableDefectMatrix, observableFrameMatrix, A, a, sigma] using
        blockJ_quadratic_eq_defect (Variational.frameMatrix sigma A) e

private theorem cutoff_observableDefectMatrix_posSemidef (M : ABKModel 2)
    (m : ℤ) (omega : Cutoff.CutoffSample 2) (Q : TriadicCube 2) :
    (observableDefectMatrix Q (Cutoff.coefficientCutoff M.nu m omega).toFun
      (Annealed.sigmaBar M m : ℝ)).PosSemidef := by
  have hHerm :
      (observableDefectMatrix Q (Cutoff.coefficientCutoff M.nu m omega).toFun
        (Annealed.sigmaBar M m : ℝ)).IsHermitian := by
    simpa [Matrix.IsHermitian, Matrix.IsSymm] using
      observableDefectMatrix_isSymm Q
        (Cutoff.coefficientCutoff M.nu m omega).toFun (Annealed.sigmaBar M m : ℝ)
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm
  intro e
  simp only [star_trivial]
  rw [← cutoff_frame_quadratic_identity M m omega Q e]
  exact Ch02.doubledResponseJ_nonneg (Ch02.cubeDomain Q)
    (Cutoff.coefficientCutoffTriadicCoeffFamily M m omega |>.coeffOn Q)
    (ofFullBlockVec (Matrix.mulVec
      (Ch02.constantFullBlockMatrixInvSqrt
        (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m))) e))
    (ofFullBlockVec (Matrix.mulVec
      (Ch02.constantFullBlockMatrixSqrt
        (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m))) e))

private theorem quadratic_le_observableMatrixNorm (A : FullBlockMat 2)
    (e : FullBlockVec 2) (he : Ch02.fullBlockVecNormSq e = 1) :
    dotProduct e (Matrix.mulVec A e) ≤ observableMatrixNorm A := by
  let x : EuclideanSpace ℝ (BlockCoord 2) := WithLp.toLp 2 e
  have hxSq : ‖x‖ ^ 2 = 1 := by
    calc
      ‖x‖ ^ 2 = ∑ i, ‖x.ofLp i‖ ^ 2 := EuclideanSpace.norm_sq_eq x
      _ = Ch02.fullBlockVecNormSq e := by
        simp [x, Ch02.fullBlockVecNormSq, Real.norm_eq_abs, sq_abs]
      _ = 1 := he
  have hx : ‖x‖ = 1 := by nlinarith [norm_nonneg x]
  have hinner :
      inner ℝ x ((Matrix.toEuclideanCLM (𝕜 := ℝ) A) x) =
        dotProduct e (Matrix.mulVec A e) := by
    simpa [x] using Matrix.inner_toEuclideanCLM A x x
  calc
    dotProduct e (Matrix.mulVec A e) =
        inner ℝ x ((Matrix.toEuclideanCLM (𝕜 := ℝ) A) x) := hinner.symm
    _ ≤ |inner ℝ x ((Matrix.toEuclideanCLM (𝕜 := ℝ) A) x)| := le_abs_self _
    _ ≤ ‖x‖ * ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) A) x‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg x)
    _ = observableMatrixNorm A := by
      rw [hx]
      simp [observableMatrixNorm]

private theorem cutoff_normalizedBlockResponseMax_le_traceDefect
    (M : ABKModel 2) (m : ℤ) (omega : Cutoff.CutoffSample 2)
    (Q : TriadicCube 2) :
    Ch02.normalizedBlockResponseMax Q
        (Cutoff.coefficientCutoffTriadicCoeffFamily M m omega)
        (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)) ≤
      traceDefect (cubeSet Q) (Cutoff.coefficientCutoff M.nu m omega).toFun
        (Annealed.sigmaBar M m : ℝ) := by
  let F : Ch02.TriadicCoeffFamily 2 :=
    Cutoff.coefficientCutoffTriadicCoeffFamily M m omega
  let a0 : Mat 2 := Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)
  let H : FullBlockMat 2 := observableDefectMatrix Q
    (Cutoff.coefficientCutoff M.nu m omega).toFun (Annealed.sigmaBar M m : ℝ)
  let e0 : FullBlockVec 2 := Pi.single (Sum.inl (0 : Fin 2)) (1 : ℝ)
  let P0 : BlockVec 2 := ofFullBlockVec
    (Matrix.mulVec (Ch02.constantFullBlockMatrixInvSqrt a0) e0)
  let P0star : BlockVec 2 := ofFullBlockVec
    (Matrix.mulVec (Ch02.constantFullBlockMatrixSqrt a0) e0)
  have he0 : Ch02.fullBlockVecNormSq e0 = 1 := by
    simp [e0, Ch02.fullBlockVecNormSq]
  have hne : (Ch02.normalizedBlockResponseValueSet Q F a0).Nonempty := by
    refine ⟨Ch02.doubledResponseJ (Ch02.cubeDomain Q) (F.coeffOn Q) P0 P0star, ?_⟩
    exact ⟨e0, he0, rfl⟩
  unfold Ch02.normalizedBlockResponseMax
  refine csSup_le hne ?_
  intro value hvalue
  rcases hvalue with ⟨e, he, rfl⟩
  calc
    _ = dotProduct e (Matrix.mulVec H e) := by
      simpa [F, H, a0] using cutoff_frame_quadratic_identity M m omega Q e
    _ ≤ observableMatrixNorm H :=
      quadratic_le_observableMatrixNorm H e he
    _ ≤ Matrix.trace H :=
      observableMatrixNorm_le_trace H
        (cutoff_observableDefectMatrix_posSemidef M m omega Q)
    _ = traceDefect (cubeSet Q) (Cutoff.coefficientCutoff M.nu m omega).toFun
        (Annealed.sigmaBar M m : ℝ) := by
      simpa [H] using observableDefectMatrix_trace Q
        (Cutoff.coefficientCutoff M.nu m omega).toFun (Annealed.sigmaBar M m : ℝ)

/-- The trace of the positive response defect is the sum of its four unit
coordinate responses. Each coordinate response occurs in the normalized
response value set. -/
private theorem cutoff_traceDefect_le_four_normalizedBlockResponseMax
    (M : ABKModel 2) (m : ℤ) (omega : Cutoff.CutoffSample 2)
    (Q : TriadicCube 2) :
    traceDefect (cubeSet Q) (Cutoff.coefficientCutoff M.nu m omega).toFun
        (Annealed.sigmaBar M m : ℝ) ≤
      4 * Ch02.normalizedBlockResponseMax Q
        (Cutoff.coefficientCutoffTriadicCoeffFamily M m omega)
        (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)) := by
  classical
  let F : Ch02.TriadicCoeffFamily 2 :=
    Cutoff.coefficientCutoffTriadicCoeffFamily M m omega
  let a0 : Mat 2 := Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)
  let H : FullBlockMat 2 := observableDefectMatrix Q
    (Cutoff.coefficientCutoff M.nu m omega).toFun (Annealed.sigmaBar M m : ℝ)
  have hroot : Q ∈ Homogenization.descendantsAtScale Q Q.scale := by simp
  have hbounded : BddAbove (Ch02.normalizedBlockResponseValueSet Q F a0) :=
    Ch02.normalizedBlockResponseValueSet_bddAbove_of_mem_descendantsAtScale
      F a0 hroot
  have hcoordinate (i : BlockCoord 2) :
      dotProduct (Pi.single i (1 : ℝ))
          (Matrix.mulVec H (Pi.single i (1 : ℝ))) ≤
        Ch02.normalizedBlockResponseMax Q F a0 := by
    let e : FullBlockVec 2 := Pi.single i (1 : ℝ)
    have he : Ch02.fullBlockVecNormSq e = 1 := by
      unfold Ch02.fullBlockVecNormSq
      rw [Fintype.sum_eq_single i]
      · simp [e]
      · intro j hji
        simp [e, hji]
    have hvalue :
        Ch02.doubledResponseJ (Ch02.cubeDomain Q) (F.coeffOn Q)
            (ofFullBlockVec (Matrix.mulVec (Ch02.constantFullBlockMatrixInvSqrt a0) e))
            (ofFullBlockVec (Matrix.mulVec (Ch02.constantFullBlockMatrixSqrt a0) e)) ∈
          Ch02.normalizedBlockResponseValueSet Q F a0 := ⟨e, he, rfl⟩
    have hidentity :
        Ch02.doubledResponseJ (Ch02.cubeDomain Q) (F.coeffOn Q)
            (ofFullBlockVec (Matrix.mulVec (Ch02.constantFullBlockMatrixInvSqrt a0) e))
            (ofFullBlockVec (Matrix.mulVec (Ch02.constantFullBlockMatrixSqrt a0) e)) =
          dotProduct e (Matrix.mulVec H e) := by
      simpa [F, a0, H, e] using cutoff_frame_quadratic_identity M m omega Q e
    have hmem : dotProduct e (Matrix.mulVec H e) ∈
        Ch02.normalizedBlockResponseValueSet Q F a0 := by
      rw [← hidentity]
      exact hvalue
    unfold Ch02.normalizedBlockResponseMax
    simpa [e] using le_csSup hbounded hmem
  have htrace :
      Matrix.trace H = ∑ i : BlockCoord 2,
        dotProduct (Pi.single i (1 : ℝ))
          (Matrix.mulVec H (Pi.single i (1 : ℝ))) := by
    simp [Matrix.trace, dotProduct, Matrix.mulVec, Pi.single_apply]
  have htraceDefect :
      traceDefect (cubeSet Q) (Cutoff.coefficientCutoff M.nu m omega).toFun
          (Annealed.sigmaBar M m : ℝ) = Matrix.trace H := by
    simpa [H] using (observableDefectMatrix_trace Q
      (Cutoff.coefficientCutoff M.nu m omega).toFun (Annealed.sigmaBar M m : ℝ)).symm
  rw [htraceDefect, htrace]
  calc
    (∑ i : BlockCoord 2,
        dotProduct (Pi.single i (1 : ℝ))
          (Matrix.mulVec H (Pi.single i (1 : ℝ)))) ≤
        ∑ _i : BlockCoord 2, Ch02.normalizedBlockResponseMax Q F a0 :=
      Finset.sum_le_sum fun i _ => hcoordinate i
    _ = 4 * Ch02.normalizedBlockResponseMax Q F a0 := by norm_num [BlockCoord]

/-- The trace-defect maximum at depth `t` below the cutoff cube of side `3^m`.
The finite supremum uses exactly the source's descendant cells. -/
noncomputable def cutoffTraceDefectMaxAtDepth (M : ABKModel 2) (m : ℤ)
    (omega : Cutoff.CutoffSample 2) (t : ℕ) : ℝ :=
  Ch02.finsetSupReal
    (Homogenization.descendantsAtScale (originCube 2 m)
      ((originCube 2 m).scale - (t : ℤ)))
    (fun Q => traceDefect (cubeSet Q) (Cutoff.coefficientCutoff M.nu m omega).toFun
      (Annealed.sigmaBar M m : ℝ))

private theorem cutoffTraceDefectMaxAtDepth_nonneg
    (M : ABKModel 2) (m : ℤ) (omega : Cutoff.CutoffSample 2) (t : ℕ) :
    0 ≤ cutoffTraceDefectMaxAtDepth M m omega t := by
  let R : TriadicCube 2 := originCube 2 m
  have hscale : R.scale - (t : ℤ) ≤ R.scale := by
    exact sub_le_self _ (by exact_mod_cast Nat.zero_le t)
  apply Ch02.finsetSupReal_nonneg
  intro Q hQ
  rw [← observableDefectMatrix_trace]
  exact Matrix.PosSemidef.trace_nonneg
    (cutoff_observableDefectMatrix_posSemidef M m omega Q)

private theorem cutoffTraceDefectMaxAtDepth_le_uniform
    (M : ABKModel 2) (m : ℤ) (omega : Cutoff.CutoffSample 2) (t : ℕ) :
    cutoffTraceDefectMaxAtDepth M m omega t ≤
      4 * Ch02.normalizedBlockResponseUniformBound (originCube 2 m)
        (Cutoff.coefficientCutoffTriadicCoeffFamily M m omega)
        (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)) := by
  let R : TriadicCube 2 := originCube 2 m
  let F : Ch02.TriadicCoeffFamily 2 :=
    Cutoff.coefficientCutoffTriadicCoeffFamily M m omega
  let a0 : Mat 2 := Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)
  have hscale : R.scale - (t : ℤ) ≤ R.scale := by
    exact sub_le_self _ (by exact_mod_cast Nat.zero_le t)
  have hnonempty := Homogenization.descendantsAtScale_nonempty R hscale
  unfold cutoffTraceDefectMaxAtDepth
  refine Ch02.finsetSupReal_le _ hnonempty ?_
  intro Q hQ
  have htrace := cutoff_traceDefect_le_four_normalizedBlockResponseMax M m omega Q
  have hresponse := Ch02.normalizedBlockResponseMax_le_uniform_of_mem_descendantsAtScale
    F a0 hQ
  calc
    traceDefect (cubeSet Q) (Cutoff.coefficientCutoff M.nu m omega).toFun
        (Annealed.sigmaBar M m : ℝ) ≤ 4 * Ch02.normalizedBlockResponseMax Q F a0 := by
      simpa [F, a0] using htrace
    _ ≤ 4 * Ch02.normalizedBlockResponseUniformBound R F a0 :=
      mul_le_mul_of_nonneg_left hresponse (by norm_num)

private theorem cutoff_uniformResponseBound_nonneg
    (M : ABKModel 2) (m : ℤ) (omega : Cutoff.CutoffSample 2) :
    0 ≤ Ch02.normalizedBlockResponseUniformBound (originCube 2 m)
      (Cutoff.coefficientCutoffTriadicCoeffFamily M m omega)
      (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)) := by
  let R : TriadicCube 2 := originCube 2 m
  let F : Ch02.TriadicCoeffFamily 2 :=
    Cutoff.coefficientCutoffTriadicCoeffFamily M m omega
  let a0 : Mat 2 := Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)
  have hroot : R ∈ Homogenization.descendantsAtScale R R.scale := by simp
  have hmax := Ch02.normalizedBlockResponseMax_nonneg R F a0
  have hle := Ch02.normalizedBlockResponseMax_le_uniform_of_mem_descendantsAtScale
    F a0 hroot
  exact le_trans hmax (by simpa [R, F, a0] using hle)

private theorem cutoffTraceDefectDepthSeries_summable
    (M : ABKModel 2) (m : ℤ) (s : ℝ) (hs : 0 < s)
    (omega : Cutoff.CutoffSample 2) :
    Summable (fun t : ℕ => Homogenization.geometricWeight s 2 t *
      cutoffTraceDefectMaxAtDepth M m omega t) := by
  let R : TriadicCube 2 := originCube 2 m
  let F : Ch02.TriadicCoeffFamily 2 :=
    Cutoff.coefficientCutoffTriadicCoeffFamily M m omega
  let a0 : Mat 2 := Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)
  let C := 4 * Ch02.normalizedBlockResponseUniformBound R F a0
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (by norm_num) (cutoff_uniformResponseBound_nonneg M m omega)
  exact Homogenization.summable_geometricWeight_mul_of_nonneg_of_le
    (by nlinarith : 0 < s * (2 : ℝ))
    (fun t => cutoffTraceDefectMaxAtDepth_nonneg M m omega t)
    (fun t => by
      simpa [C, R, F, a0] using cutoffTraceDefectMaxAtDepth_le_uniform M m omega t)

/-- The frozen cutoff homogenization observable is bounded by the geometric
depth sum of frozen trace-defect maxima in the same true frame. -/
theorem cutoffHomogenizationError_sq_le_traceDefect_depth_sum
    (M : ABKModel 2) (m : ℤ) (s : ℝ)
    (hlo : 8 * M.gamma ≤ s) (_hhi : s ≤ 1) :
    (fun omega => Observable.cutoffHomogenizationError M m ⟨s, by
      have hγ := M.shellPrefix.gamma_pos
      linarith⟩ omega ^ 2) ≤ᵐ[(Cutoff.cutoffSampleLaw M).toMeasure]
    (fun omega =>
      (1 - Real.rpow (3 : ℝ) (-2 * s)) *
        ∑' t : ℕ, Real.rpow (3 : ℝ) (-2 * s * (t : ℝ)) *
          cutoffTraceDefectMaxAtDepth M m omega t) := by
  have hs : 0 < s := by
    have hγ := M.shellPrefix.gamma_pos
    linarith
  let a0 : Mat 2 := Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)
  let R : TriadicCube 2 := originCube 2 m
  have herror := Observable.cutoffHomogenizationError_ae_eq_homogenizationErrorOnCube
    M m ⟨s, hs⟩
  filter_upwards [herror] with omega herror
  rw [herror]
  let F : Ch02.TriadicCoeffFamily 2 :=
    Cutoff.coefficientCutoffTriadicCoeffFamily M m omega
  have hsource := Ch02.homogenizationErrorOnCube_infinity_two_sq_eq_tsum R hs F a0
  rw [hsource]
  have hsumResponse : Summable (fun t : ℕ =>
      Homogenization.geometricWeight s 2 t *
        Ch02.maxDescendantNormalizedBlockResponseAtScale R
          (R.scale - (t : ℤ)) F a0) := by
    exact Ch02.summable_geometricWeight_two_mul_maxDescendantNormalizedBlockResponseAtScale
      R F a0 hs
  have hsumTrace := cutoffTraceDefectDepthSeries_summable M m s hs omega
  have hterm : ∀ t : ℕ,
      Homogenization.geometricWeight s 2 t *
          Ch02.maxDescendantNormalizedBlockResponseAtScale R
            (R.scale - (t : ℤ)) F a0 ≤
        Homogenization.geometricWeight s 2 t *
          cutoffTraceDefectMaxAtDepth M m omega t := by
    intro t
    have hweight : 0 ≤ Homogenization.geometricWeight s 2 t :=
      Homogenization.geometricWeight_nonneg t (by positivity)
    apply mul_le_mul_of_nonneg_left _ hweight
    let D := Homogenization.descendantsAtScale R (R.scale - (t : ℤ))
    have ht : (0 : ℤ) ≤ (t : ℤ) := by exact_mod_cast (Nat.zero_le t)
    have hscale : R.scale - (t : ℤ) ≤ R.scale := sub_le_self _ ht
    have hD := Homogenization.descendantsAtScale_nonempty R hscale
    change Ch02.finsetSupReal D (fun Q =>
        Ch02.normalizedBlockResponseMax Q F a0) ≤
      Ch02.finsetSupReal D (fun Q =>
        traceDefect (cubeSet Q) (Cutoff.coefficientCutoff M.nu m omega).toFun
          (Annealed.sigmaBar M m : ℝ))
    apply Ch02.finsetSupReal_mono D hD
    intro Q hQ
    exact cutoff_normalizedBlockResponseMax_le_traceDefect M m omega Q
  have hseries := Summable.tsum_le_tsum hterm hsumResponse hsumTrace
  have hrewrite :
      (1 - Real.rpow (3 : ℝ) (-2 * s)) *
          ∑' t : ℕ, Real.rpow (3 : ℝ) (-2 * s * (t : ℝ)) *
            cutoffTraceDefectMaxAtDepth M m omega t =
        ∑' t : ℕ, Homogenization.geometricWeight s 2 t *
          cutoffTraceDefectMaxAtDepth M m omega t := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro t
    simp [Homogenization.geometricWeight, Homogenization.geometricDiscount,
      show (-s * 2 : ℝ) = -2 * s by ring]
    ring
  calc
    (∑' t : ℕ, Ch02.geometricWeight s 2 t *
        Ch02.maxDescendantNormalizedBlockResponseAtScale R
          (R.scale - (t : ℤ)) F a0) ≤
      ∑' t : ℕ, Ch02.geometricWeight s 2 t *
        cutoffTraceDefectMaxAtDepth M m omega t := by
          simpa only [Ch02.geometricWeight_eq_old] using hseries
    _ = (1 - Real.rpow (3 : ℝ) (-2 * s)) *
        ∑' t : ℕ, Real.rpow (3 : ℝ) (-2 * s * (t : ℝ)) *
          cutoffTraceDefectMaxAtDepth M m omega t := by
          simpa only [Ch02.geometricWeight_eq_old] using hrewrite.symm

end ASDExplicitGamma.AllOrder
