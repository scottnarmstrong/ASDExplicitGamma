module

public import ASDExplicitGamma.Native.OldSignedAffineCorrectorBounds
public import ASDExplicitGamma.Native.OldSignedAffineReciprocal
public import ASDExplicitGamma.Native.OldSignedCellProjection
public import ASDExplicitGamma.Native.OldSignedCoarseMean
public import ASDExplicitGamma.Scalar.CellResidualPairing
public import ASDExplicitGamma.Scalar.CellEnergyCauchy
public import ASDExplicitGamma.Scalar.CellResponseTest
public import ASDExplicitGamma.Scalar.CoefficientFlux
public import ASDExplicitGamma.Triadic.VectorHaar

/-! Finite-depth flux projection bounds for the actual OLD affine minimizer. -/
@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization MeasureTheory Response Scalar Triadic Variational
open scoped BigOperators RealInnerProductSpace
open Matrix

noncomputable section

private theorem old_signed_blockMatrix_opNorm_eq_euclidean (A : BlockMat 2) :
    ‖HilbertBlockVec.applyBlockMat A‖ =
      ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) (toFullBlockMat A)‖ := by
  let T := Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) (toFullBlockMat A)
  let B := HilbertBlockVec.applyBlockMat A
  have hfullSq (Y : BlockVec 2) :
      ‖(WithLp.toLp 2 (toFullBlockVec Y) : EuclideanSpace ℝ (BlockCoord 2))‖ ^ 2 =
        blockVecDot Y Y := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ i : BlockCoord 2, (toFullBlockVec Y i) ^ 2) = _
    rw [← dotProduct_toFullBlockVec]
    simp [dotProduct, pow_two]
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound B (norm_nonneg _) ?_
    intro X
    let P := X.toBlockVec
    let x : EuclideanSpace ℝ (BlockCoord 2) :=
      WithLp.toLp 2 (toFullBlockVec P)
    have hx : ‖x‖ = ‖X‖ := by
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      change ‖(WithLp.toLp 2 (toFullBlockVec P) :
        EuclideanSpace ℝ (BlockCoord 2))‖ ^ 2 = _
      rw [hfullSq, HilbertBlockVec.norm_sq_eq_blockVecDot]
    have hTx : T x = WithLp.toLp 2
        (toFullBlockVec (blockMatVecMul A P)) := by
      simp [T, x, Matrix.toEuclideanCLM_toLp, toFullBlockVec_blockMatVecMul]
    have hY : ‖B X‖ = ‖T x‖ := by
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      rw [HilbertBlockVec.norm_sq_applyBlockMat, hTx]
      change blockVecDot (blockMatVecMul A P) (blockMatVecMul A P) = _
      rw [← hfullSq]
    calc
      ‖B X‖ = ‖T x‖ := hY
      _ ≤ ‖T‖ * ‖x‖ := T.le_opNorm x
      _ = ‖T‖ * ‖X‖ := by rw [hx]
  · let X (x : EuclideanSpace ℝ (BlockCoord 2)) :=
      HilbertBlockVec.ofBlockVec (ofFullBlockVec x.ofLp)
    have hx (x : EuclideanSpace ℝ (BlockCoord 2)) : ‖X x‖ = ‖x‖ := by
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      rw [HilbertBlockVec.norm_sq_eq_blockVecDot]
      have hx' : x = (WithLp.toLp 2
          (toFullBlockVec (ofFullBlockVec x.ofLp)) :
            EuclideanSpace ℝ (BlockCoord 2)) := by
        ext i
        cases i <;> rfl
      rw [hx', hfullSq]
      simp [X, HilbertBlockVec.toBlockVec_ofBlockVec]
    have hTx (x : EuclideanSpace ℝ (BlockCoord 2)) :
        T x = (WithLp.toLp 2
          (toFullBlockVec (blockMatVecMul A (X x).toBlockVec)) :
            EuclideanSpace ℝ (BlockCoord 2)) := by
      change (WithLp.toLp 2 ((toFullBlockMat A) *ᵥ x.ofLp) :
        EuclideanSpace ℝ (BlockCoord 2)) = _
      have hxv : toFullBlockVec (ofFullBlockVec x.ofLp) = x.ofLp := by simp
      rw [← hxv, ← toFullBlockVec_blockMatVecMul]
      congr 1
    refine ContinuousLinearMap.opNorm_le_bound T (norm_nonneg _) ?_
    intro x
    have hY : ‖B (X x)‖ = ‖T x‖ := by
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      rw [HilbertBlockVec.norm_sq_applyBlockMat, hTx x]
      exact (hfullSq (blockMatVecMul A (X x).toBlockVec)).symm
    calc
      ‖T x‖ = ‖B (X x)‖ := hY.symm
      _ ≤ ‖B‖ * ‖X x‖ := B.le_opNorm _
      _ = ‖B‖ * ‖x‖ := by rw [hx]

private theorem old_signed_coarse_affine_deviation (Q : TriadicCube 2)
    (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (P : BlockVec 2) :
    blockVecDot (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) P - P)
        (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) P - P) ≤
      2 * Scalar.fullResponseOperatorNorm Q a *
        traceDefect (openCubeSet Q) a 1 * blockVecDot P P := by
  let A : FullBlockMat 2 := toFullBlockMat (coarseBlockMatrix (openCubeSet Q) a)
  let E := EuclideanSpace ℝ (BlockCoord 2)
  let T : E →L[ℝ] E := Matrix.toEuclideanCLM (𝕜 := ℝ) A
  let X : E := WithLp.toLp 2 (toFullBlockVec P)
  have hA : A.PosDef := Cold.coarse_square_full_posDef Q hEll
  have hAinv : A⁻¹.PosDef := hA.inv
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hmulInv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hdet
  have hinvMul : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hdet
  let D : FullBlockMat 2 := (A - 1) * A⁻¹ * (A - 1)
  have hDform : D = A + A⁻¹ - 2 • (1 : FullBlockMat 2) := by
    dsimp [D]
    calc
      (A - 1) * A⁻¹ * (A - 1) = A * A⁻¹ * A - A * A⁻¹ - A⁻¹ * A + A⁻¹ := by
        noncomm_ring
      _ = A + A⁻¹ - 2 • (1 : FullBlockMat 2) := by
        rw [hmulInv, hinvMul]
        noncomm_ring
  have hD : D.PosSemidef := by
    have h := hAinv.posSemidef.conjTranspose_mul_mul_same (A - 1)
    have hconj : Matrix.conjTranspose (A - 1) = A - 1 := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hA.isHermitian.eq]
    rw [hconj] at h
    simpa [D] using h
  let Dlin : E →L[ℝ] E := Matrix.toEuclideanCLM (𝕜 := ℝ) D
  have hDsym : Dlin.toLinearMap.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hD.1
  have hDpos (x : E) : 0 ≤ ⟪x, Dlin x⟫ := by
    have h := hD.dotProduct_mulVec_nonneg x.ofLp
    rw [Cold.matrix_euclidean_inner]
    simpa only [star_trivial] using h
  have hDtrace : LinearMap.trace ℝ E Dlin.toLinearMap = D.trace := by
    change LinearMap.trace ℝ E (Matrix.toEuclideanLin D) = D.trace
    exact Cold.trace_toEuclideanLin (n := BlockCoord 2) D
  have hDnorm : ‖Dlin‖ ≤ D.trace := by
    calc
      ‖Dlin‖ ≤ LinearMap.trace ℝ E Dlin.toLinearMap :=
        Cold.norm_le_trace_of_positive_operator Dlin hDsym hDpos
      _ = D.trace := hDtrace
  let R : FullBlockMat 2 := Cold.coarseGramSwap
  have hR : R.IsHermitian := Cold.coarseGramSwap_isHermitian
  have hRR : R * R = 1 := Cold.coarseGramSwap_sq
  have hRAR : (R * A * R).IsHermitian := by
    have h := Matrix.isHermitian_conjTranspose_mul_mul R hA.isHermitian
    simpa only [hR.eq] using h
  have hOrder : (R * A * R - A⁻¹).PosSemidef := by
    apply Matrix.isPositive_toEuclideanLin_iff.mp
    constructor
    · exact Matrix.isSymmetric_toEuclideanLin_iff.mpr (hRAR.sub hAinv.isHermitian)
    · intro x
      have h := Cold.coarse_square_inverse_reflection_order Q hEll x
      change ⟪x, A⁻¹.toEuclideanLin x⟫ ≤
        ⟪x, R.toEuclideanLin (A.toEuclideanLin (R.toEuclideanLin x))⟫ at h
      simp only [Matrix.toEuclideanLin, map_sub, Matrix.toLpLin_mul_same,
        LinearMap.sub_apply, LinearMap.comp_apply, inner_sub_left,
        real_inner_comm]
      exact sub_nonneg.mpr h
  have hOrderTrace : 0 ≤ (R * A * R - A⁻¹).trace := hOrder.trace_nonneg
  have hTraceInv : A⁻¹.trace ≤ A.trace := by
    have hcyc : (R * A * R).trace = A.trace := by
      calc
      (R * A * R).trace = (A * R * R).trace := by
          calc
            (R * A * R).trace = (R * (A * R)).trace := by rw [mul_assoc]
            _ = ((A * R) * R).trace := Matrix.trace_mul_comm R (A * R)
            _ = (A * R * R).trace := by rw [mul_assoc]
        _ = A.trace := by
          rw [mul_assoc, hRR, Matrix.mul_one]
    rw [Matrix.trace_sub, hcyc] at hOrderTrace
    linarith
  have hTraceD : D.trace ≤ 2 * (A.trace - 4) := by
    have hEqTrace : D.trace = A.trace + (A⁻¹).trace - 8 := by
      rw [hDform, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul,
        Matrix.trace_one]
      norm_num [Fintype.card_sum, Fintype.card_fin, BlockCoord]
    rw [hEqTrace]
    linarith
  have hTraceEq : A.trace - 4 = traceDefect (openCubeSet Q) a 1 := by
    simp only [A, traceDefect, inv_one, one_mul, Matrix.trace, Matrix.diag_apply,
      Fintype.sum_sum_type, toFullBlockMat]
  have hDnorm' : ‖Dlin‖ ≤ 2 * traceDefect (openCubeSet Q) a 1 := by
    calc
      ‖Dlin‖ ≤ D.trace := hDnorm
      _ ≤ 2 * (A.trace - 4) := hTraceD
      _ = 2 * traceDefect (openCubeSet Q) a 1 := by rw [hTraceEq]
  let Elin : E →L[ℝ] E := Matrix.toEuclideanCLM (𝕜 := ℝ) (A - 1)
  let Mlin : E →L[ℝ] E := T.comp Dlin
  have hEform : Elin.comp Elin = Mlin := by
    let F : FullBlockMat 2 ≃⋆ₐ[ℝ] (E →L[ℝ] E) :=
      Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ)
    have hmat : (A - 1) * (A - 1) = A * D := by
      rw [hDform]
      have hright : A * (A + A⁻¹ - 2 • (1 : FullBlockMat 2)) =
          A * A + A * A⁻¹ - 2 • A := by noncomm_ring
      calc
        (A - 1) * (A - 1) = A * A - 2 • A + 1 := by noncomm_ring
        _ = A * (A + A⁻¹ - 2 • (1 : FullBlockMat 2)) := by
          rw [hright, hmulInv]
          noncomm_ring
    calc
      Elin.comp Elin = F (A - 1) * F (A - 1) := rfl
      _ = F ((A - 1) * (A - 1)) := (map_mul F (A - 1) (A - 1)).symm
      _ = F (A * D) := congrArg F hmat
      _ = F A * F D := map_mul F A D
      _ = Mlin := rfl
  have hMnorm : ‖Mlin‖ ≤ ‖T‖ * (2 * traceDefect (openCubeSet Q) a 1) := by
    calc
      ‖Mlin‖ = ‖T.comp Dlin‖ := rfl
      _ ≤ ‖T‖ * ‖Dlin‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖T‖ * (2 * traceDefect (openCubeSet Q) a 1) := by
        apply mul_le_mul_of_nonneg_left hDnorm'
        exact norm_nonneg _
  have hInner := Cold.inner_operator_le_norm_sq (Elin.comp Elin) X
  have hSymE : Elin.toLinearMap.IsSymmetric := by
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr (hA.isHermitian.sub Matrix.isHermitian_one)
  have hpoint : blockVecDot (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) P - P)
      (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) P - P) =
      ⟪X, (Elin.comp Elin) X⟫ := by
    change blockVecDot (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) P - P)
      (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) P - P) =
        ⟪X, Elin (Elin X)⟫
    have hSymPoint : ⟪Elin X, Elin X⟫ = ⟪X, Elin (Elin X)⟫ := by
      exact hSymE X (Elin X)
    rw [← hSymPoint]
    have hX : X.ofLp = toFullBlockVec P := by simp [X]
    have hRX : (Elin X).ofLp = toFullBlockVec
        (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) P - P) := by
      change (A - 1).mulVec X.ofLp = _
      rw [hX, Matrix.sub_mulVec, Matrix.one_mulVec]
      rw [← toFullBlockVec_blockMatVecMul]
      ext i
      cases i <;> rfl
    rw [EuclideanSpace.inner_eq_star_dotProduct, hRX]
    simp only [star_trivial, dotProduct_toFullBlockVec]
  have hPnorm : ⟪X, X⟫ = blockVecDot P P := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [X, star_trivial, dotProduct_toFullBlockVec]
  have hTN : ‖T‖ = Scalar.fullResponseOperatorNorm Q a := by
    calc
      ‖T‖ = ‖HilbertBlockVec.applyBlockMat
          (coarseBlockMatrix (openCubeSet Q) a)‖ := by
            change ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ)
              (toFullBlockMat (coarseBlockMatrix (openCubeSet Q) a))‖ = _
            exact (old_signed_blockMatrix_opNorm_eq_euclidean
              (coarseBlockMatrix (openCubeSet Q) a)).symm
      _ = Scalar.fullResponseOperatorNorm Q a := by
        rw [Scalar.fullResponseOperatorNorm, ← cube_coarseMatrix_eq_open Q a]
  calc
    _ = ⟪X, (Elin.comp Elin) X⟫ := hpoint
    _ ≤ ‖Elin.comp Elin‖ * ⟪X, X⟫ := hInner
    _ ≤ ‖Mlin‖ * ⟪X, X⟫ := by
      rw [hEform]
    _ ≤ (‖T‖ * (2 * traceDefect (openCubeSet Q) a 1)) * ⟪X, X⟫ :=
      mul_le_mul_of_nonneg_right hMnorm (real_inner_self_nonneg)
    _ = 2 * Scalar.fullResponseOperatorNorm Q a *
        traceDefect (openCubeSet Q) a 1 * blockVecDot P P := by
      rw [hTN, hPnorm]
      ring

private theorem old_signed_local_affine_flux_mean (Q R : TriadicCube 2)
    (depth : ℕ) (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2)
    (hR : R ∈ descendantsAtDepth Q depth) :
    oldSignedBlockMean R (fun x => scalarCoefficientFlux
      (responseFramePlanarCoefficientField nu sigma k)
      (oldSignedLocalResidual Q depth nu sigma hnu hsigma k
        (fun _ => P) (memLp_const P)) x) =
      blockMatVecMul (coarseBlockMatrix (openCubeSet R)
        (responseFramePlanarCoefficientField nu sigma k)) P := by
  classical
  let hRQ := openCubeSet_subset_of_mem_descendantsAtDepth hR
  let a := responseFramePlanarCoefficientField nu sigma k
  let kR := oldSignedCellCoefficient Q R hRQ k
  let aR := responseFramePlanarCoefficientField nu sigma kR
  let F : Vec 2 → BlockVec 2 := fun _ => P
  let hF : MemBlockL2 (openCubeSet Q) F := memLp_const P
  let L : Vec 2 → BlockVec 2 := oldSignedLocalResidual Q depth nu sigma hnu hsigma k F hF
  let Z : Vec 2 → BlockVec 2 := oldSignedCellResidual Q R hRQ nu sigma hnu hsigma k F hF
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) nu sigma hnu hsigma k
  have hEllR := hEll.mono (measurableSet_openCubeSet R) hRQ
  have hEllR' := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet R) nu sigma hnu hsigma kR
  have hL : MemBlockL2 (openCubeSet Q) L :=
    old_signed_local_residual_memLp Q depth nu sigma hnu hsigma k F hF
  have hJ : MemBlockL2 (openCubeSet Q) (scalarCoefficientFlux a L) :=
    scalar_coefficient_flux_memL2 Q a hEll hL
  have hJR : MemBlockL2 (openCubeSet R) (scalarCoefficientFlux a L) :=
    hJ.mono_measure (Measure.restrict_mono_set volume hRQ)
  have hRestr := old_signed_local_residual_restrict Q depth nu sigma hnu hsigma k
    F hF R hR
  have hRestr' : L =ᵐ[volumeMeasureOn (openCubeSet R)] Z := by
    simpa [L, Z] using hRestr
  have hFR : MemBlockL2 (openCubeSet R) F := memLp_const P
  have hFRconst : toHilbertBlockL2OfBlockField hFR =
      (scalarFrameRealization R nu sigma hnu hsigma kR).constantField P := by
    have hconst : toHilbertBlockL2OfBlockField hFR =
        blockVecToHilbertBlockL2Const P := by
      apply Lp.ext
      filter_upwards [coeFn_toHilbertBlockL2OfBlockField hFR,
        coeFn_blockVecToHilbertBlockL2Const (U := openCubeSet R) P] with x hx hy
      exact hx.trans hy.symm
    exact hconst.trans (by rfl)
  have hZ : Z = scalarResidualField R nu sigma hnu hsigma kR
      ((scalarFrameRealization R nu sigma hnu hsigma kR).constantField P) := by
    funext x
    change scalarResidualField R nu sigma hnu hsigma kR
      (toHilbertBlockL2OfBlockField hFR) x = _
    rw [hFRconst]
  have hCoeffMat (x : Vec 2) (hx : x ∈ openCubeSet R) : aR x = a x := by
    simp only [aR, a, responseFramePlanarCoefficientField]
    rw [old_signed_cell_coefficient_extension_eq Q R hRQ k hx]
  have hCoeff (x : Vec 2) (hx : x ∈ openCubeSet R) :
      blockCoeffField aR x = blockCoeffField a x := by
    simpa [blockCoeffField] using congrArg blockMatrixOfCoeff (hCoeffMat x hx)
  have hCoeffAE : aR =ᵐ[volume.restrict (openCubeSet R)] a := by
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet R)] with x hx
    exact hCoeffMat x hx
  have hCoarse := coarseBlockMatrix_congr_of_ae_eq hCoeffAE
  have hCan := old_signed_affine_residual_field R nu sigma hnu hsigma kR P
  let C : BlockVec 2 → ℝ := fun V => blockVecDot V
    (blockMatVecMul (coarseBlockMatrix (openCubeSet R) a) P)
  have htest (V : BlockVec 2) :
      volumeAverage (openCubeSet R) (fun x => blockVecDot V
        (scalarCoefficientFlux a L x)) = C V := by
    have hAE : (fun x => blockVecDot V (scalarCoefficientFlux a L x)) =ᵐ[
        volumeMeasureOn (openCubeSet R)]
        (fun x => blockVecDot V (blockMatVecMul (blockCoeffField aR x)
          (oldSignedCanonicalAffineField R aR hEllR' P x))) := by
      filter_upwards [hRestr', ae_restrict_mem (measurableSet_openCubeSet R)]
        with x hLx hx
      have hfield : L x = oldSignedCanonicalAffineField R aR hEllR' P x := by
        calc
          L x = Z x := hLx
          _ = scalarResidualField R nu sigma hnu hsigma kR
              ((scalarFrameRealization R nu sigma hnu hsigma kR).constantField P) x :=
            congrArg (fun G : Vec 2 → BlockVec 2 => G x) hZ
          _ = oldSignedCanonicalAffineField R aR hEllR' P x :=
            congrArg (fun U : BlockL2 (openCubeSet R) => U x) hCan
      change blockVecDot V (blockMatVecMul (blockCoeffField a x) (L x)) = _
      rw [← hCoeff x hx, hfield]
    have havg : volumeAverage (openCubeSet R)
        (fun x => blockVecDot V (scalarCoefficientFlux a L x)) =
        volumeAverage (openCubeSet R) (fun x => blockVecDot V
          (blockMatVecMul (blockCoeffField aR x)
            (oldSignedCanonicalAffineField R aR hEllR' P x))) := by
      unfold volumeAverage
      congr 1
      exact integral_congr_ae hAE
    calc
      volumeAverage (openCubeSet R) (fun x => blockVecDot V
          (scalarCoefficientFlux a L x)) =
        volumeAverage (openCubeSet R) (fun x => blockVecDot V
          (blockMatVecMul (blockCoeffField aR x)
            (oldSignedCanonicalAffineField R aR hEllR' P x))) := havg
      _ = blockVecDot V (blockMatVecMul
          (coarseBlockMatrix (openCubeSet R) aR) P) :=
        old_signed_affine_field_constant_test R aR hEllR' P V
      _ = C V := by rw [hCoarse]
  have hmean (V : BlockVec 2) :
      blockVecDot V (oldSignedBlockMean R (scalarCoefficientFlux a L)) = C V := by
    rw [← old_signed_constant_block_pairing_mean R hJR V]
    exact htest V
  apply Prod.ext
  · funext i
    have h := hmean (basisVec i, 0)
    simpa [blockVecDot, vecDot_zero_left, zero_add, vecDot_basisVec_left, C] using h
  · funext i
    have h := hmean (0, basisVec i)
    simpa [blockVecDot, vecDot_zero_left, zero_add, vecDot_basisVec_left, C] using h

private theorem old_signed_pairing_integrable_R (Q : TriadicCube 2)
    (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    {F G : Vec 2 → BlockVec 2}
    (hF : MemBlockL2 (openCubeSet Q) F) (hG : MemBlockL2 (openCubeSet Q) G) :
    IntegrableOn (fun x => blockVecDot (F x)
      (blockMatVecMul (blockCoeffField a x) (G x))) (openCubeSet Q) := by
  have hflux := scalar_coefficient_flux_memL2 Q a hEll hG
  have hfirst := integrableOn_vecDot_of_memVectorL2
    (memVectorL2_fst_of_memBlockL2 hF) (memVectorL2_fst_of_memBlockL2 hflux)
  have hsecond := integrableOn_vecDot_of_memVectorL2
    (memVectorL2_snd_of_memBlockL2 hF) (memVectorL2_snd_of_memBlockL2 hflux)
  have hsum : IntegrableOn (fun x =>
      vecDot (F x).1 (scalarCoefficientFlux a G x).1 +
      vecDot (F x).2 (scalarCoefficientFlux a G x).2) (openCubeSet Q) :=
    hfirst.add hsecond
  exact hsum.congr_fun_ae <| Filter.Eventually.of_forall fun x => by
    simp [scalarCoefficientFlux, blockVecDot]

private theorem old_signed_cubeAverage_add_R (Q : TriadicCube 2)
    {f g : Vec 2 → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hg : MemLp g 2 (normalizedCubeMeasure Q)) :
    cubeAverage Q (fun x => f x + g x) = cubeAverage Q f + cubeAverage Q g := by
  rw [cubeAverage_eq_integral_normalizedCubeMeasure,
    cubeAverage_eq_integral_normalizedCubeMeasure,
    cubeAverage_eq_integral_normalizedCubeMeasure]
  exact integral_add (hf.integrable (by norm_num)) (hg.integrable (by norm_num))

private theorem old_signed_block_mean_add_R (Q : TriadicCube 2)
    {F G : Vec 2 → BlockVec 2}
    (hF : MemBlockL2 (openCubeSet Q) F) (hG : MemBlockL2 (openCubeSet Q) G) :
    oldSignedBlockMean Q (fun x => F x + G x) =
      oldSignedBlockMean Q F + oldSignedBlockMean Q G := by
  apply Prod.ext
  · funext i
    change cubeAverage Q (fun x => (F x).1 i + (G x).1 i) = _
    exact old_signed_cubeAverage_add_R Q
      (memLp_normalized_of_memL2On
        (memScalarL2_coord_of_memVectorL2 (memVectorL2_fst_of_memBlockL2 hF) i))
      (memLp_normalized_of_memL2On
        (memScalarL2_coord_of_memVectorL2 (memVectorL2_fst_of_memBlockL2 hG) i))
  · funext i
    change cubeAverage Q (fun x => (F x).2 i + (G x).2 i) = _
    exact old_signed_cubeAverage_add_R Q
      (memLp_normalized_of_memL2On
        (memScalarL2_coord_of_memVectorL2 (memVectorL2_snd_of_memBlockL2 hF) i))
      (memLp_normalized_of_memL2On
        (memScalarL2_coord_of_memVectorL2 (memVectorL2_snd_of_memBlockL2 hG) i))

private theorem old_signed_block_mean_const_R (Q : TriadicCube 2) (P : BlockVec 2) :
    oldSignedBlockMean Q (fun _ => P) = P := by
  apply Prod.ext <;> funext i <;>
    simp [oldSignedBlockMean, cubeAverage_const]

private theorem old_signed_block_mean_sub_const_R (Q : TriadicCube 2)
    {F : Vec 2 → BlockVec 2} (hF : MemBlockL2 (openCubeSet Q) F)
    (P : BlockVec 2) :
    oldSignedBlockMean Q (fun x => F x - P) = oldSignedBlockMean Q F - P := by
  have hadd := old_signed_block_mean_add_R Q hF (memLp_const (-P))
  have hfield : (fun x => F x - P) = (fun x => F x + (-P)) := by
    funext x
    exact sub_eq_add_neg _ _
  rw [hfield, hadd, old_signed_block_mean_const_R]
  rfl

private theorem old_signed_blockVecDot_add_self_le_R (X Y : BlockVec 2) :
    blockVecDot (X + Y) (X + Y) ≤
      2 * blockVecDot X X + 2 * blockVecDot Y Y := by
  have hnonneg := blockVecDot_nonneg (X - Y)
  have hexpand : blockVecDot (X - Y) (X - Y) =
      blockVecDot X X - 2 * blockVecDot X Y + blockVecDot Y Y := by
    have hleft : blockVecDot (X - Y) X = blockVecDot X X - blockVecDot X Y := by
      rw [blockVecDot_comm, blockVecDot_sub_right]
    have hright : blockVecDot (X - Y) Y = blockVecDot X Y - blockVecDot Y Y := by
      rw [blockVecDot_comm, blockVecDot_sub_right, blockVecDot_comm Y X]
    rw [blockVecDot_sub_right, hleft, hright]
    ring
  have hsum : blockVecDot (X + Y) (X + Y) =
      blockVecDot X X + 2 * blockVecDot X Y + blockVecDot Y Y := by
    simp only [blockVecDot_add_left, blockVecDot_add_right]
    rw [blockVecDot_comm Y X]
    ring
  rw [hexpand] at hnonneg
  rw [hsum]
  nlinarith

private theorem old_signed_patch_flux_mean_difference_bound
    (Q R : TriadicCube 2) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2)
    (hR : R ∈ descendantsAtDepth Q depth) :
    blockVecDot (oldSignedBlockMean R (fun x =>
      scalarCoefficientFlux (responseFramePlanarCoefficientField nu sigma k)
        (fun y => scalarResidualField Q nu sigma hnu hsigma k
          ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField P) y -
          oldSignedLocalResidual Q depth nu sigma hnu hsigma k (fun _ => P)
            (memLp_const P) y) x))
      (oldSignedBlockMean R (fun x =>
        scalarCoefficientFlux (responseFramePlanarCoefficientField nu sigma k)
          (fun y => scalarResidualField Q nu sigma hnu hsigma k
            ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField P) y -
            oldSignedLocalResidual Q depth nu sigma hnu hsigma k (fun _ => P)
              (memLp_const P) y) x)) ≤
      Scalar.fullResponseDepthMax Q (responseFramePlanarCoefficientField nu sigma k) depth *
        volumeAverage (openCubeSet R) (fun x => blockVecDot
          (scalarResidualField Q nu sigma hnu hsigma k
            ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField P) x -
            oldSignedLocalResidual Q depth nu sigma hnu hsigma k (fun _ => P)
              (memLp_const P) x)
          (blockMatVecMul
            (blockCoeffField (responseFramePlanarCoefficientField nu sigma k) x)
            (scalarResidualField Q nu sigma hnu hsigma k
              ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField P) x -
              oldSignedLocalResidual Q depth nu sigma hnu hsigma k (fun _ => P)
                (memLp_const P) x))) := by
  classical
  let hRQ := openCubeSet_subset_of_mem_descendantsAtDepth hR
  let a := responseFramePlanarCoefficientField nu sigma k
  let H := (scalarFrameRealization Q nu sigma hnu hsigma k).constantField P
  let S : Vec 2 → BlockVec 2 := scalarResidualField Q nu sigma hnu hsigma k H
  let L : Vec 2 → BlockVec 2 := oldSignedLocalResidual Q depth nu sigma hnu hsigma k
    (fun _ => P) (memLp_const P)
  let D : Vec 2 → BlockVec 2 := fun x => S x - L x
  let hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) nu sigma hnu hsigma k
  let hEllR := hEll.mono (measurableSet_openCubeSet R) hRQ
  have hS : MemBlockL2 (openCubeSet Q) S := Lp.memLp _
  have hL : MemBlockL2 (openCubeSet Q) L :=
    old_signed_local_residual_memLp Q depth nu sigma hnu hsigma k
      (fun _ => P) (memLp_const P)
  have hD : MemBlockL2 (openCubeSet Q) D := hS.sub hL
  have hDR : MemBlockL2 (openCubeSet R) D :=
    hD.mono_measure (Measure.restrict_mono_set volume hRQ)
  have hFluxD : MemBlockL2 (openCubeSet R) (scalarCoefficientFlux a D) := by
    have hFlux := scalar_coefficient_flux_memL2 Q a hEll hD
    exact hFlux.mono_measure (Measure.restrict_mono_set volume hRQ)
  let X := oldSignedBlockMean R (scalarCoefficientFlux a D)
  let T : Vec 2 → BlockVec 2 := (scalarCellResponseTest R a hEllR X).eval
  let W : Vec 2 → BlockVec 2 := fun x => T x - X
  have hT : MemBlockL2 (openCubeSet R) T := scalar_cell_response_test_memL2 R a hEllR X
  have hW : MemBlockL2 (openCubeSet R) W := hT.sub (memLp_const X)
  have hWvar : ScalarVariation (openCubeSet R) W :=
    scalar_cell_response_test_variation R a hEllR X
  let kR := oldSignedCellCoefficient Q R hRQ k
  let aR := responseFramePlanarCoefficientField nu sigma kR
  let H_R := (scalarFrameRealization R nu sigma hnu hsigma kR).constantField P
  let Z := oldSignedCellResidual Q R hRQ nu sigma hnu hsigma k (fun _ => P)
    (memLp_const P)
  have hRestr := old_signed_local_residual_restrict Q depth nu sigma hnu hsigma k
    (fun _ => P) (memLp_const P) R hR
  have hRestr' : L =ᵐ[volumeMeasureOn (openCubeSet R)] Z := by
    simpa [L, Z] using hRestr
  have hFconst : MemBlockL2 (openCubeSet R) (fun _ : Vec 2 => P) := memLp_const P
  have hFconst' : toHilbertBlockL2OfBlockField hFconst = H_R := by
    have hconst : toHilbertBlockL2OfBlockField hFconst =
        blockVecToHilbertBlockL2Const P := by
      apply Lp.ext
      filter_upwards [coeFn_toHilbertBlockL2OfBlockField hFconst,
        coeFn_blockVecToHilbertBlockL2Const (U := openCubeSet R) P] with x hx hy
      exact hx.trans hy.symm
    exact hconst.trans (by rfl)
  have hZ : Z = scalarResidualField R nu sigma hnu hsigma kR H_R := by
    change scalarResidualField R nu sigma hnu hsigma kR
      (toHilbertBlockL2OfBlockField hFconst) = _
    rw [hFconst']
  have hCoeff (x : Vec 2) (hx : x ∈ openCubeSet R) :
      blockCoeffField aR x = blockCoeffField a x := by
    simp only [aR, a, responseFramePlanarCoefficientField, blockCoeffField]
    rw [old_signed_cell_coefficient_extension_eq Q R hRQ k hx]
  have hLocalOrth : volumeAverage (openCubeSet R) (fun x =>
      blockVecDot (W x) (blockMatVecMul (blockCoeffField a x) (L x))) = 0 := by
    have horth := scalar_residual_field_orthogonal R nu sigma hnu hsigma kR H_R W hWvar
    have hAE : (fun x => blockVecDot (W x)
        (blockMatVecMul (blockCoeffField a x) (L x))) =ᵐ[
          volumeMeasureOn (openCubeSet R)]
        (fun x => blockVecDot (W x)
          (blockMatVecMul (blockCoeffField aR x)
            (scalarResidualField R nu sigma hnu hsigma kR H_R x))) := by
      filter_upwards [hRestr', ae_restrict_mem (measurableSet_openCubeSet R)]
        with x hLx hx
      rw [hCoeff x hx, hLx, hZ]
    unfold volumeAverage at horth ⊢
    rw [integral_congr_ae hAE]
    exact horth
  have hParentOrth : volumeAverage (openCubeSet R) (fun x =>
      blockVecDot (W x) (blockMatVecMul (blockCoeffField a x) (S x))) = 0 :=
    scalar_residual_local_orthogonal Q R hRQ nu sigma hnu hsigma k H W hWvar
  have hIntParent := old_signed_pairing_integrable_R R a hEllR hW
    (hS.mono_measure (Measure.restrict_mono_set volume hRQ))
  have hIntLocal := old_signed_pairing_integrable_R R a hEllR hW
    (hL.mono_measure (Measure.restrict_mono_set volume hRQ))
  have hDorth : volumeAverage (openCubeSet R) (fun x =>
      blockVecDot (W x) (blockMatVecMul (blockCoeffField a x) (D x))) = 0 := by
    have hpoint (x : Vec 2) : blockVecDot (W x)
        (blockMatVecMul (blockCoeffField a x) (D x)) =
        blockVecDot (W x) (blockMatVecMul (blockCoeffField a x) (S x)) -
          blockVecDot (W x) (blockMatVecMul (blockCoeffField a x) (L x)) := by
      change blockVecDot (W x)
        (blockMatVecMul (blockCoeffField a x) (S x - L x)) = _
      rw [sub_eq_add_neg, blockMatVecMul_add]
      have hneg : -L x = (-1 : ℝ) • L x := by simp
      rw [hneg, blockMatVecMul_smul, neg_one_smul, ← sub_eq_add_neg,
        blockVecDot_sub_right]
    calc
      _ = volumeAverage (openCubeSet R) (fun x =>
          blockVecDot (W x) (blockMatVecMul (blockCoeffField a x) (S x)) -
            blockVecDot (W x) (blockMatVecMul (blockCoeffField a x) (L x))) := by
              congr 1
              funext x
              exact hpoint x
      _ = 0 := by
        calc
          volumeAverage (openCubeSet R) (fun x =>
              blockVecDot (W x) (blockMatVecMul (blockCoeffField a x) (S x)) -
                blockVecDot (W x) (blockMatVecMul (blockCoeffField a x) (L x))) =
            volumeAverage (openCubeSet R) (fun x =>
              blockVecDot (W x) (blockMatVecMul (blockCoeffField a x) (S x))) -
              volumeAverage (openCubeSet R) (fun x =>
                blockVecDot (W x) (blockMatVecMul (blockCoeffField a x) (L x))) :=
                  volumeAverage_sub hIntParent hIntLocal
          _ = 0 := by rw [hParentOrth, hLocalOrth]; ring
  have hIntT := old_signed_pairing_integrable_R R a hEllR hT hDR
  have hIntX := old_signed_pairing_integrable_R R a hEllR (memLp_const X) hDR
  have hIntW := old_signed_pairing_integrable_R R a hEllR hW hDR
  have hPairT : volumeAverage (openCubeSet R) (fun x =>
      blockVecDot (T x) (blockMatVecMul (blockCoeffField a x) (D x))) =
      blockVecDot X X := by
    have hMean := old_signed_constant_block_pairing_mean R hFluxD X
    have hsub := volumeAverage_sub hIntT hIntX
    have hWpoint (x : Vec 2) : blockVecDot (W x)
        (blockMatVecMul (blockCoeffField a x) (D x)) =
        blockVecDot (T x) (blockMatVecMul (blockCoeffField a x) (D x)) -
          blockVecDot X (blockMatVecMul (blockCoeffField a x) (D x)) := by
      change blockVecDot (T x - X)
        (blockMatVecMul (blockCoeffField a x) (D x)) = _
      calc
        _ = blockVecDot (blockMatVecMul (blockCoeffField a x) (D x)) (T x - X) :=
          blockVecDot_comm _ _
        _ = blockVecDot (blockMatVecMul (blockCoeffField a x) (D x)) (T x) -
            blockVecDot (blockMatVecMul (blockCoeffField a x) (D x)) X :=
          blockVecDot_sub_right _ _ _
        _ = blockVecDot (blockMatVecMul (blockCoeffField a x) (D x)) (T x) -
            blockVecDot X (blockMatVecMul (blockCoeffField a x) (D x)) := by
          rw [blockVecDot_comm (blockMatVecMul (blockCoeffField a x) (D x)) X]
        _ = blockVecDot (T x) (blockMatVecMul (blockCoeffField a x) (D x)) -
            blockVecDot X (blockMatVecMul (blockCoeffField a x) (D x)) := by
          exact congrArg (fun z : ℝ => z - blockVecDot X
            (blockMatVecMul (blockCoeffField a x) (D x)))
            (blockVecDot_comm (blockMatVecMul (blockCoeffField a x) (D x)) (T x))
    have hzero : volumeAverage (openCubeSet R) (fun x =>
        blockVecDot (T x) (blockMatVecMul (blockCoeffField a x) (D x))) -
          volumeAverage (openCubeSet R) (fun x =>
            blockVecDot X (blockMatVecMul (blockCoeffField a x) (D x))) = 0 := by
      calc
        _ = volumeAverage (openCubeSet R) (fun x =>
            blockVecDot (T x) (blockMatVecMul (blockCoeffField a x) (D x)) -
              blockVecDot X (blockMatVecMul (blockCoeffField a x) (D x))) := hsub.symm
        _ = volumeAverage (openCubeSet R) (fun x =>
            blockVecDot (W x) (blockMatVecMul (blockCoeffField a x) (D x))) := by
              congr 1
              funext x
              exact (hWpoint x).symm
        _ = 0 := hDorth
    have hMean' : volumeAverage (openCubeSet R) (fun x =>
        blockVecDot X (blockMatVecMul (blockCoeffField a x) (D x))) = blockVecDot X X := by
      simpa [scalarCoefficientFlux, X] using hMean
    rw [hMean'] at hzero
    linarith
  have hCauchy := scalar_cell_field_cauchy R a hEllR hDR hT
  have hTE := scalar_cell_response_test_energy R a hEllR X
  rw [cube_coarseMatrix_eq_open] at hTE
  have hOp := Scalar.block_quadratic_le_operator_norm
    (coarseBlockMatrix (cubeSet R) a) X
  have hOp' : blockVecDot X (blockMatVecMul
      (coarseBlockMatrix (cubeSet R) a) X) ≤
      Scalar.fullResponseOperatorNorm R a * blockVecDot X X := by
    simpa only [Scalar.fullResponseOperatorNorm] using hOp
  have hMax := Scalar.full_response_norm_le_depth_max Q R a depth hR
  have hOpOpen : blockVecDot X (blockMatVecMul
      (coarseBlockMatrix (openCubeSet R) a) X) ≤
      Scalar.fullResponseOperatorNorm R a * blockVecDot X X := by
    simpa only [cube_coarseMatrix_eq_open] using hOp'
  have hE_T : volumeAverage (openCubeSet R) (fun x =>
      blockVecDot (T x) (blockMatVecMul (blockCoeffField a x) (T x))) ≤
      Scalar.fullResponseDepthMax Q a depth * blockVecDot X X := by
    calc
      volumeAverage (openCubeSet R) (fun x =>
          blockVecDot (T x) (blockMatVecMul (blockCoeffField a x) (T x))) =
        blockVecDot X (blockMatVecMul (coarseBlockMatrix (openCubeSet R) a) X) := hTE
      _ ≤ Scalar.fullResponseDepthMax Q a depth * blockVecDot X X :=
        hOpOpen.trans (mul_le_mul_of_nonneg_right hMax (blockVecDot_nonneg X))
  have hEnergyNonneg : 0 ≤ volumeAverage (openCubeSet R) (fun x =>
      blockVecDot (D x) (blockMatVecMul (blockCoeffField a x) (D x))) :=
    scalar_coefficient_energy_average_nonneg R a hEllR D
  have hNormNonneg : 0 ≤ blockVecDot X X := blockVecDot_nonneg X
  have hCauchy' : (blockVecDot X X) ^ 2 ≤
      volumeAverage (openCubeSet R) (fun x =>
        blockVecDot (D x) (blockMatVecMul (blockCoeffField a x) (D x))) *
        (Scalar.fullResponseDepthMax Q a depth * blockVecDot X X) := by
    calc
      (blockVecDot X X) ^ 2 =
          (volumeAverage (openCubeSet R) (fun x =>
            blockVecDot (T x) (blockMatVecMul (blockCoeffField a x) (D x)))) ^ 2 := by
              rw [hPairT]
      _ ≤ volumeAverage (openCubeSet R) (fun x =>
            blockVecDot (D x) (blockMatVecMul (blockCoeffField a x) (D x))) *
          volumeAverage (openCubeSet R) (fun x =>
            blockVecDot (T x) (blockMatVecMul (blockCoeffField a x) (T x))) := hCauchy
      _ ≤ volumeAverage (openCubeSet R) (fun x =>
            blockVecDot (D x) (blockMatVecMul (blockCoeffField a x) (D x))) *
          (Scalar.fullResponseDepthMax Q a depth * blockVecDot X X) :=
            mul_le_mul_of_nonneg_left hE_T hEnergyNonneg
  change blockVecDot X X ≤ Scalar.fullResponseDepthMax Q a depth *
    volumeAverage (openCubeSet R) (fun x =>
      blockVecDot (D x) (blockMatVecMul (blockCoeffField a x) (D x)))
  by_cases hX : blockVecDot X X = 0
  · rw [hX]
    exact mul_nonneg (Scalar.full_response_depth_max_nonneg Q a depth) hEnergyNonneg
  · have hXpos : 0 < blockVecDot X X := lt_of_le_of_ne hNormNonneg (Ne.symm hX)
    nlinarith [hCauchy']

private theorem old_signed_block_projection_energy_eq_means
    (Q : TriadicCube 2) (j : ℕ) (F : Vec 2 → BlockVec 2)
    (hF : ∀ b : Bool, ∀ i : Fin 2,
      MemLp (fun x => (if b then (F x).1 else (F x).2) i) 2
        (normalizedCubeMeasure Q)) :
    (∑ i, energy Q (cubeProjection Q j (fun x => (F x).1 i))) +
      (∑ i, energy Q (cubeProjection Q j (fun x => (F x).2 i))) =
    descendantsAverage Q j (fun R =>
      blockVecDot (oldSignedBlockMean R F) (oldSignedBlockMean R F)) := by
  have hfst := vector_projection_energy_eq_means Q j (fun x => (F x).1)
    (fun i => hF true i)
  have hsnd := vector_projection_energy_eq_means Q j (fun x => (F x).2)
    (fun i => hF false i)
  rw [hfst, hsnd]
  unfold descendantsAverage
  calc
    ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth Q j,
          vecNormSq (fun i => cubeAverage R (fun x => (F x).1 i)) +
            ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth Q j,
          vecNormSq (fun i => cubeAverage R (fun x => (F x).2 i)) =
      ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
        ((∑ R ∈ descendantsAtDepth Q j,
            vecNormSq (fun i => cubeAverage R (fun x => (F x).1 i))) +
          ∑ R ∈ descendantsAtDepth Q j,
            vecNormSq (fun i => cubeAverage R (fun x => (F x).2 i))) := by ring
    _ = ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth Q j,
          (vecNormSq (fun i => cubeAverage R (fun x => (F x).1 i)) +
            vecNormSq (fun i => cubeAverage R (fun x => (F x).2 i))) := by
      rw [Finset.sum_add_distrib]
    _ = ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth Q j,
          blockVecDot (oldSignedBlockMean R F) (oldSignedBlockMean R F) := by
      congr 1

/-- Every finite depth of the actual affine reciprocal error is controlled by
the exact OLD trace increment and the full response depth maximum. -/
theorem old_signed_affine_reciprocal_projection_bound (Q : TriadicCube 2)
    (depth : ℕ) (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    (∑ i, energy Q (cubeProjection Q depth (fun x =>
      (scalarCoefficientFlux (responseFramePlanarCoefficientField nu sigma k)
        (scalarResidualField Q nu sigma hnu hsigma k
          ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField P)) x - P).1 i))) +
      (∑ i, energy Q (cubeProjection Q depth (fun x =>
        (scalarCoefficientFlux (responseFramePlanarCoefficientField nu sigma k)
          (scalarResidualField Q nu sigma hnu hsigma k
            ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField P)) x - P).2 i))) ≤
    6 * Scalar.fullResponseDepthMax Q
        (responseFramePlanarCoefficientField nu sigma k) depth *
      descendantsAverage Q depth (fun R => traceDefect (openCubeSet R)
        (responseFramePlanarCoefficientField nu sigma k) 1) * blockVecDot P P := by
  classical
  let a := responseFramePlanarCoefficientField nu sigma k
  let H := (scalarFrameRealization Q nu sigma hnu hsigma k).constantField P
  let S : Vec 2 → BlockVec 2 := scalarResidualField Q nu sigma hnu hsigma k H
  let L : Vec 2 → BlockVec 2 := oldSignedLocalResidual Q depth nu sigma hnu hsigma k
    (fun _ => P) (memLp_const P)
  let D : Vec 2 → BlockVec 2 := fun x => S x - L x
  let J : Vec 2 → BlockVec 2 := fun x => scalarCoefficientFlux a S x - P
  let JD : Vec 2 → BlockVec 2 := scalarCoefficientFlux a D
  let JL : Vec 2 → BlockVec 2 := scalarCoefficientFlux a L
  let d (j : ℕ) := descendantsAverage Q j
    (fun R => traceDefect (openCubeSet R) a 1)
  let b (j : ℕ) := Scalar.fullResponseDepthMax Q a j
  let p := blockVecDot P P
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) nu sigma hnu hsigma k
  have hS : MemBlockL2 (openCubeSet Q) S := Lp.memLp _
  have hL : MemBlockL2 (openCubeSet Q) L :=
    old_signed_local_residual_memLp Q depth nu sigma hnu hsigma k
      (fun _ => P) (memLp_const P)
  have hD : MemBlockL2 (openCubeSet Q) D := hS.sub hL
  have hFluxS : MemBlockL2 (openCubeSet Q) (scalarCoefficientFlux a S) :=
    scalar_coefficient_flux_memL2 Q a hEll hS
  have hJ : MemBlockL2 (openCubeSet Q) J := hFluxS.sub (memLp_const P)
  have hJD : MemBlockL2 (openCubeSet Q) JD :=
    scalar_coefficient_flux_memL2 Q a hEll hD
  have hJL : MemBlockL2 (openCubeSet Q) JL :=
    scalar_coefficient_flux_memL2 Q a hEll hL
  have hSplit : J = fun x => JD x + (JL x - P) := by
    funext x
    change blockMatVecMul (blockCoeffField a x) (S x) - P =
      blockMatVecMul (blockCoeffField a x) (S x - L x) +
        (blockMatVecMul (blockCoeffField a x) (L x) - P)
    have hlin : blockMatVecMul (blockCoeffField a x) (S x - L x) =
        blockMatVecMul (blockCoeffField a x) (S x) -
          blockMatVecMul (blockCoeffField a x) (L x) := by
      rw [sub_eq_add_neg, blockMatVecMul_add]
      have hneg : -L x = (-1 : ℝ) • L x := by simp
      rw [hneg, blockMatVecMul_smul, neg_one_smul, ← sub_eq_add_neg]
    rw [hlin]
    abel
  have hcoords : ∀ (b : Bool) (i : Fin 2),
      MemLp (fun x => (if b then (J x).1 else (J x).2) i) 2
        (normalizedCubeMeasure Q) := by
    intro b i
    cases b
    · exact memLp_normalized_of_memL2On
        (memScalarL2_coord_of_memVectorL2 (memVectorL2_snd_of_memBlockL2 hJ) i)
    · exact memLp_normalized_of_memL2On
        (memScalarL2_coord_of_memVectorL2 (memVectorL2_fst_of_memBlockL2 hJ) i)
  have hProjMean := old_signed_block_projection_energy_eq_means Q depth J hcoords
  have hCell (R : TriadicCube 2) (hR : R ∈ descendantsAtDepth Q depth) :
      blockVecDot (oldSignedBlockMean R J) (oldSignedBlockMean R J) ≤
        2 * b depth * volumeAverage (openCubeSet R) (fun x =>
          blockVecDot (D x) (blockMatVecMul (blockCoeffField a x) (D x))) +
        4 * b depth * traceDefect (openCubeSet R) a 1 * p := by
    let hRQ := openCubeSet_subset_of_mem_descendantsAtDepth hR
    let hEllR := hEll.mono (measurableSet_openCubeSet R) hRQ
    let X := oldSignedBlockMean R JD
    let dev := blockMatVecMul (coarseBlockMatrix (openCubeSet R) a) P - P
    have hMeanL := old_signed_local_affine_flux_mean Q R depth nu sigma
      hnu hsigma k P hR
    have hMeanL' : oldSignedBlockMean R JL =
        blockMatVecMul (coarseBlockMatrix (openCubeSet R) a) P := by
      simpa [JL, a, L] using hMeanL
    have hJDR : MemBlockL2 (openCubeSet R) JD :=
      hJD.mono_measure (Measure.restrict_mono_set volume hRQ)
    have hJL_R : MemBlockL2 (openCubeSet R) JL :=
      hJL.mono_measure (Measure.restrict_mono_set volume hRQ)
    have hJLminusR : MemBlockL2 (openCubeSet R) (fun x => JL x - P) :=
      hJL_R.sub (memLp_const P)
    have hMeanJD := old_signed_block_mean_add_R R
      hJDR hJLminusR
    have hMeanSplit : oldSignedBlockMean R J = X + dev := by
      calc
        oldSignedBlockMean R J = oldSignedBlockMean R (fun x => JD x + (JL x - P)) := by
          rw [hSplit]
        _ = oldSignedBlockMean R JD + oldSignedBlockMean R (fun x => JL x - P) := hMeanJD
        _ = X + dev := by
          rw [old_signed_block_mean_sub_const_R R hJL_R P, hMeanL']
    have hX := old_signed_patch_flux_mean_difference_bound Q R depth
      nu sigma hnu hsigma k P hR
    have hX' : blockVecDot X X ≤ b depth *
        volumeAverage (openCubeSet R) (fun x =>
          blockVecDot (D x) (blockMatVecMul (blockCoeffField a x) (D x))) := by
      simpa [X, b, a, S, L, D] using hX
    have hdev := old_signed_coarse_affine_deviation R a hEllR P
    have hdev' : blockVecDot dev dev ≤
        2 * b depth * traceDefect (openCubeSet R) a 1 * p := by
      have hmax := Scalar.full_response_norm_le_depth_max Q R a depth hR
      have htrace := Cold.coarse_square_traceDefect_nonneg R hEllR
      have hp : 0 ≤ p := blockVecDot_nonneg P
      calc
        blockVecDot dev dev ≤
            2 * Scalar.fullResponseOperatorNorm R a *
              traceDefect (openCubeSet R) a 1 * p := by
                simpa [dev, p] using hdev
        _ = (2 * Scalar.fullResponseOperatorNorm R a) *
              (traceDefect (openCubeSet R) a 1 * p) := by ring
        _ ≤ (2 * b depth) * (traceDefect (openCubeSet R) a 1 * p) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hmax (by norm_num))
            (mul_nonneg htrace hp)
        _ = 2 * b depth * traceDefect (openCubeSet R) a 1 * p := by ring
    have hsum := old_signed_blockVecDot_add_self_le_R X dev
    have hK : 0 ≤ b depth := Scalar.full_response_depth_max_nonneg Q a depth
    have hE : 0 ≤ volumeAverage (openCubeSet R) (fun x =>
        blockVecDot (D x) (blockMatVecMul (blockCoeffField a x) (D x))) :=
      scalar_coefficient_energy_average_nonneg R a hEllR D
    rw [hMeanSplit]
    calc
      blockVecDot (X + dev) (X + dev) ≤ 2 * blockVecDot X X + 2 * blockVecDot dev dev := hsum
      _ ≤ 2 * b depth * volumeAverage (openCubeSet R) (fun x =>
            blockVecDot (D x) (blockMatVecMul (blockCoeffField a x) (D x))) +
          4 * b depth * traceDefect (openCubeSet R) a 1 * p := by
            nlinarith [hX', hdev']
  have hMeans := descendantsAverage_le (Q := Q) (j := depth) hCell
  let E : Vec 2 → ℝ := fun x => blockVecDot (D x)
    (blockMatVecMul (blockCoeffField a x) (D x))
  have hEint : IntegrableOn E (openCubeSet Q) := by
    exact scalar_coefficient_energy_integrable Q a hEll hD
  have hPartition := old_signed_volumeAverage_descendants Q depth E hEint
  have hAvgEnergy : oldSignedEnergyPairing Q nu sigma k D D =
      descendantsAverage Q depth (fun R => volumeAverage (openCubeSet R) E) := by
    change volumeAverage (openCubeSet Q) E = _
    exact hPartition
  have hPatch := old_signed_affine_patch_trace_gap_bound Q depth nu sigma
    hnu hsigma k P
  have hTrace0 : 0 ≤ traceDefect (openCubeSet Q) a 1 :=
    Cold.coarse_square_traceDefect_nonneg Q hEll
  have hp : 0 ≤ p := blockVecDot_nonneg P
  have hAvgEbound : descendantsAverage Q depth
      (fun R => volumeAverage (openCubeSet R) E) ≤ d depth * p := by
    calc
      descendantsAverage Q depth (fun R => volumeAverage (openCubeSet R) E) =
          oldSignedEnergyPairing Q nu sigma k D D := hAvgEnergy.symm
      _ ≤ (d depth - traceDefect (openCubeSet Q) a 1) * p := by
            simpa [d, D, S, L, a, E] using hPatch
      _ ≤ d depth * p := by
            apply mul_le_mul_of_nonneg_right _ hp
            linarith
  have hTraceAvgNonneg : 0 ≤ d depth := by
    apply descendantsAverage_nonneg Q depth _
    intro R hR
    have hsub := openCubeSet_subset_of_mem_descendantsAtDepth hR
    have hEllR := hEll.mono (measurableSet_openCubeSet R) hsub
    exact Cold.coarse_square_traceDefect_nonneg R hEllR
  have hK : 0 ≤ b depth := Scalar.full_response_depth_max_nonneg Q a depth
  have hAvgMeansBound : descendantsAverage Q depth
      (fun R => blockVecDot (oldSignedBlockMean R J) (oldSignedBlockMean R J)) ≤
      6 * b depth * d depth * p := by
    calc
      _ ≤ descendantsAverage Q depth (fun R =>
          2 * b depth * volumeAverage (openCubeSet R) E +
            4 * b depth * traceDefect (openCubeSet R) a 1 * p) := hMeans
      _ = 2 * b depth * descendantsAverage Q depth
            (fun R => volumeAverage (openCubeSet R) E) +
          4 * b depth * d depth * p := by
            rw [descendantsAverage_add]
            have hEavg := descendantsAverage_mul_left Q depth (2 * b depth)
              (fun R => volumeAverage (openCubeSet R) E)
            have hTavg : descendantsAverage Q depth (fun R =>
                4 * b depth * traceDefect (openCubeSet R) a 1 * p) =
                4 * b depth * p * descendantsAverage Q depth
                  (fun R => traceDefect (openCubeSet R) a 1) := by
              calc
                _ = descendantsAverage Q depth (fun R =>
                    (4 * b depth * p) * traceDefect (openCubeSet R) a 1) := by
                      congr 1
                      funext R
                      ring
                _ = _ := descendantsAverage_mul_left Q depth (4 * b depth * p)
                  (fun R => traceDefect (openCubeSet R) a 1)
            rw [hEavg, hTavg]
            dsimp [d]
            ring
      _ ≤ 2 * b depth * (d depth * p) + 4 * b depth * d depth * p := by
            exact add_le_add (mul_le_mul_of_nonneg_left hAvgEbound (by positivity)) le_rfl
      _ = 6 * b depth * d depth * p := by ring
  rw [hProjMean]
  simpa [a, b, d, p] using hAvgMeansBound

private theorem old_signed_trace_history_toReal_recip (Q : TriadicCube 2)
    (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    Inverse.rawWeakTraceHistory (fun j => descendantsAverage Q j
      (fun R => traceDefect (openCubeSet R) a 1)) =
      (oldSignedTraceHistory Q a).toReal := by
  let α := Scalar.inverseHistoryDiscount
  let d (j : ℕ) := descendantsAverage Q j
    (fun R => traceDefect (openCubeSet R) a 1)
  have hα : 0 ≤ α := Scalar.inverse_history_discount_range.1.le
  have h1α : 0 ≤ 1 - α := sub_nonneg.mpr Scalar.inverse_history_discount_range.2.le
  have hTrace : Summable (fun j : ℕ => α ^ j * d j) := by
    simpa [α, d] using old_signed_trace_depth_series_summable Q a hEll
  have hTerm (j : ℕ) : 0 ≤ α ^ j * d j := by
    have hEllR (R : TriadicCube 2) (hR : R ∈ descendantsAtDepth Q j) :
        IsEllipticFieldOn lam Lam (openCubeSet R) a :=
      hEll.mono (measurableSet_openCubeSet R)
        (openCubeSet_subset_of_mem_descendantsAtDepth hR)
    have hD : 0 ≤ d j := by
      apply descendantsAverage_nonneg Q j _
      intro R hR
      exact ASDExplicitGamma.Cold.coarse_square_traceDefect_nonneg R (hEllR R hR)
    exact mul_nonneg (pow_nonneg hα j) hD
  have hSumNonneg : 0 ≤ ∑' j : ℕ, α ^ j * d j := tsum_nonneg hTerm
  have hSeriesENN : (∑' j : ℕ, ENNReal.ofReal (α ^ j * d j)) =
      ENNReal.ofReal (∑' j : ℕ, α ^ j * d j) :=
    (ENNReal.ofReal_tsum_of_nonneg hTerm hTrace).symm
  have hHistoryENN : oldSignedTraceHistory Q a =
      ENNReal.ofReal ((1 - α) * ∑' j : ℕ, α ^ j * d j) := by
    unfold oldSignedTraceHistory
    rw [hSeriesENN]
    rw [← ENNReal.ofReal_mul h1α]
  unfold Inverse.rawWeakTraceHistory
  rw [hHistoryENN, ENNReal.toReal_ofReal (mul_nonneg h1α hSumNonneg)]

private theorem old_signed_vector_weak_projection_representation_R
    (Q : TriadicCube 2) (F : Vec 2 → Fin 2 → ℝ)
    (hF : ∀ i : Fin 2,
      MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q)) :
    Summable (fun j : ℕ => Scalar.inverseHistoryDiscount ^ (2 * j) *
      (∑ i, energy Q (cubeProjection Q j (fun x => F x i)))) ∧
    vectorWeakHaarEnergy Q F =
      (1 - Scalar.inverseHistoryDiscount ^ 2) *
        ∑' j : ℕ, Scalar.inverseHistoryDiscount ^ (2 * j) *
          (∑ i, energy Q (cubeProjection Q j (fun x => F x i))) := by
  classical
  let α := Scalar.inverseHistoryDiscount
  have hq : (1 : ℝ) < Real.sqrt 3 := by
    have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg (3 : ℝ)]
  have hBaseSq : Scalar.sourceHaarBase ^ 2 = Real.sqrt 3 := by
    rw [Scalar.sourceHaarBase, Real.sqrt_eq_rpow,
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    norm_num
  have hBaseInv : Scalar.sourceHaarBase⁻¹ = α := by
    dsimp [α]
    exact Scalar.inverse_history_discount_eq.symm
  have hInvSqrt : (Real.sqrt 3)⁻¹ = α ^ 2 := by
    have h := congrArg (fun x : ℝ => x⁻¹) hBaseSq
    rw [← inv_pow, hBaseInv] at h
    exact h.symm
  have hCoordSummable (i : Fin 2) : Summable (fun j : ℕ =>
      ((Real.sqrt 3)⁻¹) ^ j * energy Q (cubeProjection Q j (fun x => F x i))) :=
    summable_weighted_projections Q hq (hF i)
  have hAlphaCoordSummable (i : Fin 2) : Summable (fun j : ℕ =>
      α ^ (2 * j) * energy Q (cubeProjection Q j (fun x => F x i))) := by
    simpa only [hInvSqrt, ← pow_mul] using hCoordSummable i
  let e (j : ℕ) := ∑ i, energy Q (cubeProjection Q j (fun x => F x i))
  have hEnergySummable : Summable (fun j : ℕ => α ^ (2 * j) * e j) := by
    simp_rw [e, Finset.mul_sum]
    exact summable_sum fun i hi => hAlphaCoordSummable i
  have hRep : vectorWeakHaarEnergy Q F =
      (1 - (Real.sqrt 3)⁻¹) * ∑' j : ℕ,
        ((Real.sqrt 3)⁻¹) ^ j *
          (∑ i, energy Q (cubeProjection Q j (fun x => F x i))) := by
    simp_rw [vectorWeakHaarEnergy, dualEnergy_eq Q hq (hF _)]
    rw [← Finset.mul_sum,
      ← Summable.tsum_finsetSum (fun i _ => hCoordSummable i)]
    congr 1
    exact tsum_congr fun j => (Finset.mul_sum _ _ _).symm
  refine ⟨?_, ?_⟩
  · simpa [α, e] using hEnergySummable
  · rw [hRep, hInvSqrt]
    congr 1
    apply tsum_congr
    intro j
    have hpow : (α ^ 2) ^ j = α ^ (2 * j) := by rw [← pow_mul]
    rw [hpow]

/-- The reciprocal-gradient corrector of the actual OLD affine minimizer has
the exact six-times response/trace-history bound used by AN §6.2. -/
theorem old_signed_affine_reciprocal_corrector (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    (oldSignedBlockWeakNorm Q (fun x =>
      blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField nu sigma k) x)
        (scalarResidualField Q nu sigma hnu hsigma k
          ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField P) x) - P)) ^ 2 ≤
      6 * oldSignedCorrectorHistory Q
        (responseFramePlanarCoefficientField nu sigma k) * blockVecDot P P := by
  classical
  let α := Scalar.inverseHistoryDiscount
  let a := responseFramePlanarCoefficientField nu sigma k
  let H := (scalarFrameRealization Q nu sigma hnu hsigma k).constantField P
  let S : Vec 2 → BlockVec 2 := scalarResidualField Q nu sigma hnu hsigma k H
  let F : Vec 2 → BlockVec 2 := fun x =>
    scalarCoefficientFlux a S x - P
  let b (j : ℕ) := Scalar.fullResponseDepthMax Q a j
  let d (j : ℕ) := descendantsAverage Q j
    (fun R => traceDefect (openCubeSet R) a 1)
  let e₁ (j : ℕ) := ∑ i, energy Q (cubeProjection Q j (fun x => (F x).1 i))
  let e₂ (j : ℕ) := ∑ i, energy Q (cubeProjection Q j (fun x => (F x).2 i))
  let e (j : ℕ) := e₁ j + e₂ j
  let p := blockVecDot P P
  let G₁ : Vec 2 → Fin 2 → ℝ := fun x i => (F x).1 i
  let G₂ : Vec 2 → Fin 2 → ℝ := fun x i => (F x).2 i
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) nu sigma hnu hsigma k
  have hS : MemBlockL2 (openCubeSet Q) S := Lp.memLp _
  have hFlux : MemBlockL2 (openCubeSet Q) (scalarCoefficientFlux a S) :=
    scalar_coefficient_flux_memL2 Q a hEll hS
  have hF : MemBlockL2 (openCubeSet Q) F := hFlux.sub (memLp_const P)
  have hG₁ : ∀ i : Fin 2, MemLp (fun x => G₁ x i) 2
      (normalizedCubeMeasure Q) := by
    intro i
    exact memLp_normalized_of_memL2On
      (memScalarL2_coord_of_memVectorL2 (memVectorL2_fst_of_memBlockL2 hF) i)
  have hG₂ : ∀ i : Fin 2, MemLp (fun x => G₂ x i) 2
      (normalizedCubeMeasure Q) := by
    intro i
    exact memLp_normalized_of_memL2On
      (memScalarL2_coord_of_memVectorL2 (memVectorL2_snd_of_memBlockL2 hF) i)
  have hRep₁ := old_signed_vector_weak_projection_representation_R Q G₁ hG₁
  have hRep₂ := old_signed_vector_weak_projection_representation_R Q G₂ hG₂
  have hα : 0 ≤ α := Scalar.inverse_history_discount_range.1.le
  have hαlt : α < 1 := Scalar.inverse_history_discount_range.2
  have hα2 : 0 ≤ 1 - α ^ 2 := by
    apply sub_nonneg.mpr
    exact (pow_le_one₀ hα hαlt.le)
  have hSeries₁ : Summable (fun j : ℕ => α ^ (2 * j) * e₁ j) := by
    simpa [α, G₁, e₁] using hRep₁.1
  have hSeries₂ : Summable (fun j : ℕ => α ^ (2 * j) * e₂ j) := by
    simpa [α, G₂, e₂] using hRep₂.1
  have hBlockNorm₁ : (vectorWeakHaarNorm Q (fun x => (F x).1)) ^ 2 =
      vectorWeakHaarEnergy Q (fun x => (F x).1) := by
    rw [vectorWeakHaarNorm]
    exact Real.sq_sqrt (vectorWeakHaarEnergy_nonneg Q _)
  have hBlockNorm₂ : (vectorWeakHaarNorm Q (fun x => (F x).2)) ^ 2 =
      vectorWeakHaarEnergy Q (fun x => (F x).2) := by
    rw [vectorWeakHaarNorm]
    exact Real.sq_sqrt (vectorWeakHaarEnergy_nonneg Q _)
  have hOuter : 0 ≤ (vectorWeakHaarNorm Q (fun x => (F x).1) ^ 2) +
      (vectorWeakHaarNorm Q (fun x => (F x).2) ^ 2) :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hBlockEnergy : (oldSignedBlockWeakNorm Q F) ^ 2 =
      vectorWeakHaarEnergy Q (fun x => (F x).1) +
        vectorWeakHaarEnergy Q (fun x => (F x).2) := by
    unfold oldSignedBlockWeakNorm
    rw [Real.sq_sqrt hOuter, hBlockNorm₁, hBlockNorm₂]
  have hEnergy : (oldSignedBlockWeakNorm Q F) ^ 2 =
      (1 - α ^ 2) * ∑' j : ℕ, α ^ (2 * j) * e j := by
    rw [hBlockEnergy, hRep₁.2, hRep₂.2]
    have hsum := hSeries₁.tsum_add hSeries₂
    calc
      _ = (1 - α ^ 2) *
          ((∑' j : ℕ, α ^ (2 * j) * e₁ j) +
            ∑' j : ℕ, α ^ (2 * j) * e₂ j) := by ring
      _ = (1 - α ^ 2) * ∑' j : ℕ,
          (α ^ (2 * j) * e₁ j + α ^ (2 * j) * e₂ j) := by rw [← hsum]
      _ = (1 - α ^ 2) * ∑' j : ℕ, α ^ (2 * j) * e j := by
        congr 1
        apply tsum_congr
        intro j
        simp [e, mul_add]
  have hP : 0 ≤ p := blockVecDot_nonneg P
  have hTnonneg : ∀ j, 0 ≤ d j := by
    intro j
    apply descendantsAverage_nonneg Q j _
    intro R hR
    have hsub := openCubeSet_subset_of_mem_descendantsAtDepth hR
    have hEllR := hEll.mono (measurableSet_openCubeSet R) hsub
    exact Cold.coarse_square_traceDefect_nonneg R hEllR
  have hTsum : Summable (fun j : ℕ => α ^ j * d j) := by
    simpa [α, d] using old_signed_trace_depth_series_summable Q a hEll
  have hdepth (j : ℕ) : α ^ j * b j ≤ oldSignedResponseHistory Q a := by
    simpa [α, b] using old_signed_response_depth_discount_bound Q a hEll j
  have hProxySummable : Summable (fun j : ℕ => α ^ (2 * j) * b j * d j) := by
    apply Summable.of_nonneg_of_le
    · intro j
      exact mul_nonneg (mul_nonneg (pow_nonneg hα _)
        (Scalar.full_response_depth_max_nonneg Q a j)) (hTnonneg j)
    · intro j
      have hweight : α ^ (2 * j) * b j * d j ≤
          oldSignedResponseHistory Q a * (α ^ j * d j) := by
        calc
          α ^ (2 * j) * b j * d j = (α ^ j * b j) * (α ^ j * d j) := by
            rw [show 2 * j = j + j by omega, pow_add]
            ring
          _ ≤ oldSignedResponseHistory Q a * (α ^ j * d j) :=
            mul_le_mul_of_nonneg_right (hdepth j)
              (mul_nonneg (pow_nonneg hα j) (hTnonneg j))
      exact hweight
    · exact hTsum.mul_left (oldSignedResponseHistory Q a)
  have hProxyP : Summable (fun j : ℕ => α ^ (2 * j) * b j * d j * p) :=
    hProxySummable.mul_right p
  have hProj (j : ℕ) : e j ≤ 6 * b j * d j * p := by
    have h := old_signed_affine_reciprocal_projection_bound Q j nu sigma
      hnu hsigma k P
    simpa [e, e₁, e₂, b, d, a, p, F] using h
  have hWeakProxy : (oldSignedBlockWeakNorm Q F) ^ 2 ≤
      6 * Inverse.rawWeakTraceProxy b d * p := by
    have hSeriesE : Summable (fun j : ℕ => α ^ (2 * j) * e j) := by
      simpa [e, mul_add] using hSeries₁.add hSeries₂
    have hterm (j : ℕ) : α ^ (2 * j) * e j ≤
        6 * (α ^ (2 * j) * b j * d j * p) := by
      calc
        α ^ (2 * j) * e j ≤ α ^ (2 * j) * (6 * b j * d j * p) :=
          mul_le_mul_of_nonneg_left (hProj j) (pow_nonneg hα _)
        _ = 6 * (α ^ (2 * j) * b j * d j * p) := by ring
    have hsum := hSeriesE.tsum_le_tsum hterm (hProxyP.mul_left 6)
    calc
      (oldSignedBlockWeakNorm Q F) ^ 2 =
          (1 - α ^ 2) * ∑' j : ℕ, α ^ (2 * j) * e j := hEnergy
      _ ≤ (1 - α ^ 2) * (6 * ∑' j : ℕ, α ^ (2 * j) * b j * d j * p) :=
        mul_le_mul_of_nonneg_left (by simpa only [tsum_mul_left] using hsum) hα2
      _ = 6 * Inverse.rawWeakTraceProxy b d * p := by
        unfold Inverse.rawWeakTraceProxy
        rw [tsum_mul_right]
        ring
  have hRaw := Inverse.raw_weak_trace_proxy_le b d
    (oldSignedResponseHistory Q a) hdepth hTnonneg hProxySummable hTsum
  have hTraceHistory := old_signed_trace_history_toReal_recip Q a hEll
  calc
    (oldSignedBlockWeakNorm Q F) ^ 2 ≤ 6 * Inverse.rawWeakTraceProxy b d * p := hWeakProxy
    _ ≤ 6 * ((1 + α) * oldSignedResponseHistory Q a *
        Inverse.rawWeakTraceHistory d) * p := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hRaw (by norm_num)) hP
    _ = 6 * ((1 + α) * oldSignedResponseHistory Q a *
        (oldSignedTraceHistory Q a).toReal) * p := by rw [hTraceHistory]
    _ = 6 * oldSignedCorrectorHistory Q a * p := by
      rw [oldSignedCorrectorHistory]

end
end ASDExplicitGamma.Native
