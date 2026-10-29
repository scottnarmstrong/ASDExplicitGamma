module

public import ASDExplicitGamma.Scalar.AnalyticBlockBound
public import ASDExplicitGamma.Scalar.FullResponseNorm
public import ASDExplicitGamma.Variational.AdapterDuality
public import ASDExplicitGamma.Inverse.FullResponseTrace
public import ASDExplicitGamma.Scalar.FullResponseHistory
public import ASDExplicitGamma.Inverse.RawTraceHistory
public import ASDExplicitGamma.Model.Cutoff
public import ASDExplicitGamma.Cold.CoefficientFrame
public import ASDExplicitGamma.Gaussian.ModelHeatResponse
public import Homogenization.Book.Ch05.Theorems.Section56.VarianceEstimateQuadratic.MatrixTools
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-! The operator-norm form of the deterministic scalar analytic bound. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization Matrix ASDExplicitGamma.Variational ASDExplicitGamma.Inverse
  ASDExplicitGamma.Scalar
open ASDExplicitGamma.Model ASDExplicitGamma.Cold ASDExplicitGamma.Gaussian
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped Matrix.Norms.L2Operator ENNReal

private theorem block_apply_opNorm_le_full_matrix_opNorm (A : BlockMat 2) :
    ‖HilbertBlockVec.applyBlockMat A‖ ≤
      ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) (toFullBlockMat A)‖ := by
  let T := Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) (toFullBlockMat A)
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) ?_
  intro X
  let P := X.toBlockVec
  let x : EuclideanSpace ℝ (BlockCoord 2) := WithLp.toLp 2 (toFullBlockVec P)
  have hfullSq (Y : BlockVec 2) :
      ‖(WithLp.toLp 2 (toFullBlockVec Y) : EuclideanSpace ℝ (BlockCoord 2))‖ ^ 2 =
        blockVecDot Y Y := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ i : BlockCoord 2, (toFullBlockVec Y i) ^ 2) = _
    rw [← dotProduct_toFullBlockVec]
    simp [dotProduct, pow_two]
  have hx : ‖x‖ = ‖X‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖(WithLp.toLp 2 (toFullBlockVec P) : EuclideanSpace ℝ (BlockCoord 2))‖ ^ 2 = _
    rw [hfullSq, HilbertBlockVec.norm_sq_eq_blockVecDot]
  have hTx : T x = WithLp.toLp 2 (toFullBlockVec (blockMatVecMul A P)) := by
    simp [T, x, Matrix.toEuclideanCLM_toLp, toFullBlockVec_blockMatVecMul]
  have hY : ‖HilbertBlockVec.applyBlockMat A X‖ = ‖T x‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [HilbertBlockVec.norm_sq_applyBlockMat, hTx]
    change blockVecDot (blockMatVecMul A P) (blockMatVecMul A P) = _
    rw [← hfullSq]
  calc
    ‖HilbertBlockVec.applyBlockMat A X‖ = ‖T x‖ := hY
    _ ≤ ‖T‖ * ‖x‖ := T.le_opNorm x
    _ = ‖T‖ * ‖X‖ := by rw [hx]

private theorem full_matrix_opNorm_le_block_apply (A : BlockMat 2) :
    ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) (toFullBlockMat A)‖ ≤
      ‖HilbertBlockVec.applyBlockMat A‖ := by
  let T := Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) (toFullBlockMat A)
  let B := HilbertBlockVec.applyBlockMat A
  let X (x : EuclideanSpace ℝ (BlockCoord 2)) :=
    HilbertBlockVec.ofBlockVec (ofFullBlockVec x.ofLp)
  have hfullSq (Y : BlockVec 2) :
      ‖(WithLp.toLp 2 (toFullBlockVec Y) : EuclideanSpace ℝ (BlockCoord 2))‖ ^ 2 =
        blockVecDot Y Y := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ i : BlockCoord 2, (toFullBlockVec Y i) ^ 2) = _
    rw [← dotProduct_toFullBlockVec]
    simp [dotProduct, pow_two]
  have hx (x : EuclideanSpace ℝ (BlockCoord 2)) : ‖X x‖ = ‖x‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [HilbertBlockVec.norm_sq_eq_blockVecDot]
    have hx' : x = (WithLp.toLp 2 (toFullBlockVec (ofFullBlockVec x.ofLp)) :
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
    have hxv : toFullBlockVec (ofFullBlockVec x.ofLp) = x.ofLp := by
      simp
    rw [← hxv, ← toFullBlockVec_blockMatVecMul]
    congr 1
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) ?_
  intro x
  have hY : ‖B (X x)‖ = ‖T x‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [HilbertBlockVec.norm_sq_applyBlockMat, hTx x]
    exact (hfullSq (blockMatVecMul A (X x).toBlockVec)).symm
  calc
    ‖T x‖ = ‖B (X x)‖ := hY.symm
    _ ≤ ‖B‖ * ‖X x‖ := B.le_opNorm _
    _ = ‖B‖ * ‖x‖ := by rw [hx]

theorem block_apply_opNorm_eq_full_matrix_opNorm (A : BlockMat 2) :
    ‖HilbertBlockVec.applyBlockMat A‖ =
      ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) (toFullBlockMat A)‖ :=
  le_antisymm (block_apply_opNorm_le_full_matrix_opNorm A)
    (full_matrix_opNorm_le_block_apply A)

private theorem full_matrix_opNorm_le_analytic_bound
    (A : FullBlockMat 2) (hA : A.PosDef)
    (hdual : (A - scalarBlockSwap * A⁻¹ * scalarBlockSwap).PosSemidef) :
    ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) A‖ ≤
      1 + 2 * (A.trace - 4) + Real.sqrt (2 * (A.trace - 4)) := by
  let T := A.trace - 4
  have hs := scalar_analytic_bound A hA hdual
  have hT : 0 ≤ T := hs.1
  have hC : 0 ≤ 1 + 2 * T + Real.sqrt (2 * T) := by positivity
  let hHerm := hA.isHermitian
  let D : FullBlockMat 2 := Matrix.diagonal hHerm.eigenvalues
  have hspectral : A = Unitary.conjStarAlgAut ℝ _ hHerm.eigenvectorUnitary D := by
    simpa [D] using hHerm.spectral_theorem
  calc
    ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) A‖ = ‖A‖ :=
      Matrix.l2_opNorm_toEuclideanCLM A
    _ = ‖Unitary.conjStarAlgAut ℝ _ hHerm.eigenvectorUnitary D‖ :=
      congrArg (fun B : FullBlockMat 2 => ‖B‖) hspectral
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
    _ ≤ 1 + 2 * T + Real.sqrt (2 * T) := by
      refine (pi_norm_le_iff_of_nonneg hC).mpr ?_
      intro i
      have heig0 : 0 ≤ hHerm.eigenvalues i := (hA.eigenvalues_pos i).le
      have heigmax : hHerm.eigenvalues i ≤ largestHermitianEigenvalue A hHerm := by
        exact Finset.le_sup' (fun j => hHerm.eigenvalues j) (Finset.mem_univ i)
      calc
        ‖hHerm.eigenvalues i‖ = hHerm.eigenvalues i := by
          rw [Real.norm_eq_abs, abs_of_nonneg heig0]
        _ ≤ largestHermitianEigenvalue A hHerm := heigmax
        _ ≤ 1 + 2 * T + Real.sqrt (2 * T) := hs.2

private theorem block_duality_to_analytic_duality (A : BlockMat 2)
    (hA : IsSymmetricBlockMat A)
    (hdual : BlockMatLoewnerLE (ofFullBlockMat ((toFullBlockMat A)⁻¹)) (blockReflect A)) :
    (toFullBlockMat A - scalarBlockSwap * (toFullBlockMat A)⁻¹ * scalarBlockSwap).PosSemidef := by
  have hInvHerm : ((toFullBlockMat A)⁻¹).IsHermitian := by
    have hA' : (toFullBlockMat A).IsHermitian := by
      have hsymm := isSymm_toFullBlockMat_of_isSymmetricBlockMat hA
      simpa [Matrix.IsHermitian, Matrix.IsSymm] using hsymm
    exact hA'.inv
  have hInvSym : IsSymmetricBlockMat (ofFullBlockMat ((toFullBlockMat A)⁻¹)) := by
    apply isSymmetricBlockMat_of_isSymm
    change ((toFullBlockMat A)⁻¹).transpose = (toFullBlockMat A)⁻¹
    rw [Matrix.transpose_nonsing_inv]
    exact congrArg Inv.inv (isSymm_toFullBlockMat_of_isSymmetricBlockMat hA).eq
  have hReflectSym : IsSymmetricBlockMat (blockReflect A) := isSymmetricBlockMat_blockReflect hA
  have hreflect : toFullBlockMat (blockReflect A) =
      scalarBlockSwap * toFullBlockMat A * scalarBlockSwap := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [scalarBlockSwap, blockReflect, toFullBlockMat, Matrix.mul_apply,
        Fintype.sum_sum_type, Fin.sum_univ_two]
  have hpsd := Homogenization.Book.Ch05.Section56.transpose_blockSub_posSemidef_of_blockMatLoewnerLE
    scalarBlockSwap hdual hInvSym hReflectSym
  have hswap : scalarBlockSwap * scalarBlockSwap = 1 := by
    calc
      scalarBlockSwap * scalarBlockSwap = scalarBlockSwapᵀ * scalarBlockSwap := by
        rw [scalarBlockSwap_transpose]
      _ = 1 := scalarBlockSwap_orthogonal
  have hquad : scalarBlockSwap * (scalarBlockSwap * toFullBlockMat A * scalarBlockSwap) *
      scalarBlockSwap = toFullBlockMat A := by
    calc
      scalarBlockSwap * (scalarBlockSwap * toFullBlockMat A * scalarBlockSwap) * scalarBlockSwap =
          (scalarBlockSwap * scalarBlockSwap) * toFullBlockMat A *
            (scalarBlockSwap * scalarBlockSwap) := by noncomm_ring
      _ = toFullBlockMat A := by rw [hswap]; simp
  have hRemainder :
      scalarBlockSwap * (scalarBlockSwap * toFullBlockMat A * scalarBlockSwap -
          (toFullBlockMat A)⁻¹) * scalarBlockSwap =
        toFullBlockMat A - scalarBlockSwap * (toFullBlockMat A)⁻¹ * scalarBlockSwap := by
    calc
      scalarBlockSwap * (scalarBlockSwap * toFullBlockMat A * scalarBlockSwap -
          (toFullBlockMat A)⁻¹) * scalarBlockSwap =
        scalarBlockSwap * (scalarBlockSwap * toFullBlockMat A * scalarBlockSwap) * scalarBlockSwap -
          scalarBlockSwap * (toFullBlockMat A)⁻¹ * scalarBlockSwap := by noncomm_ring
      _ = toFullBlockMat A - scalarBlockSwap * (toFullBlockMat A)⁻¹ * scalarBlockSwap := by
        rw [hquad]
  have hmatrix :
      scalarBlockSwapᵀ * (toFullBlockMat (blockReflect A) - (toFullBlockMat A)⁻¹) *
          scalarBlockSwap =
        toFullBlockMat A - scalarBlockSwap * (toFullBlockMat A)⁻¹ * scalarBlockSwap := by
    rw [scalarBlockSwap_transpose, hreflect]
    exact hRemainder
  simp only [toFullBlockMat_ofFullBlockMat] at hpsd
  rw [hmatrix] at hpsd
  exact hpsd

/-- The actual four-dimensional coarse response operator is bounded by the
source analytic expression in its trace-defect variable. The inverse-duality
input is discharged by VA-COARSE-DUALITY, while the scalar bound is
SC-ANALYTIC-BOUND-M. -/
theorem main_full_response_operator_norm_le_trace_bound
    (Q : TriadicCube 2) {ν Λ : ℝ} {a : CoeffField 2}
    (hν : 0 < ν) (hEll : IsEllipticFieldOn ν Λ (cubeSet Q) a) :
    fullResponseOperatorNorm Q a ≤
      1 + 2 * traceDefect (cubeSet Q) a 1 +
        Real.sqrt (2 * traceDefect (cubeSet Q) a 1) := by
  let B := coarseBlockMatrix (cubeSet Q) a
  let A := toFullBlockMat B
  have hA : A.PosDef := coarseBlockMatrix_posDef hν hEll
  have hDualBlock := coarseBlockMatrix_inverse_duality hν hEll
  have hDual := block_duality_to_analytic_duality B (coarseBlockMatrix_symmetric _ _) hDualBlock
  have hMatrix := full_matrix_opNorm_le_analytic_bound A hA hDual
  have hnorm := block_apply_opNorm_le_full_matrix_opNorm B
  have htrace : traceDefect (cubeSet Q) a 1 = A.trace - 4 := by
    rw [traceDefect_eq_full_framedTrace]
    simp [A, B, frameMatrix]
  simpa [fullResponseOperatorNorm, A, B, htrace] using hnorm.trans hMatrix

/-- The pointwise source multiplier bound for the actual partial insertion in
the fixed OLD frame.  The field is normalized by `sigmaBar⁻¹`; `cold_coarse_frame`
identifies its coarse matrix with the source framed matrix, while
`main_full_response_operator_norm_le_trace_bound` supplies the analytic
estimate from VA-COARSE-DUALITY and SC-ANALYTIC-BOUND-M. -/
theorem main_partial_inserted_response_norm_le_raw_trace
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (t : ℝ)
    (ht : 0 ≤ t ∧ t ≤ 1) (ω : Cutoff.CutoffSample 2) :
    fullResponseOperatorNorm Q
        ((Annealed.sigmaBar M m : ℝ)⁻¹ •
          (Model.partialInsertedCoefficient M m t ω).toFun) ≤
      1 + 2 * rawCubeFourLoadTrace M m Q t ω +
        Real.sqrt (2 * rawCubeFourLoadTrace M m Q t ω) := by
  let σ : ℝ := Annealed.sigmaBar M m
  let a : CoeffField 2 := (Model.partialInsertedCoefficient M m t ω).toFun
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
  let K : Set (Vec 2) := closure (cubeSet Q)
  have hK : IsCompact K := (isBounded_cubeSet Q).isCompact_closure
  obtain ⟨ell, hEllCover⟩ := Gaussian.exists_originCube_containing_compact K hK
  have hCube : cubeSet Q ⊆ openCubeSet (originCube 2 ell) := by
    intro x hx
    exact hEllCover (subset_closure hx)
  have hEll := Model.partialInsertedCoefficient_isEllipticFieldOn M ell m ω ht
    (measurableSet_cubeSet Q) hCube
  have hEllFrame := ASDExplicitGamma.Cold.cold_isEllipticFieldOn_smul
    (inv_pos.mpr hσ) hEll
  have hTrace : traceDefect (cubeSet Q)
      ((σ⁻¹ : ℝ) • a) 1 = rawCubeFourLoadTrace M m Q t ω := by
    have hFrame := ASDExplicitGamma.Cold.cold_coarse_frame M.nu_pos hEll hσ
    have hTraceFrame : traceDefect (cubeSet Q)
        ((σ⁻¹ : ℝ) • a) 1 = traceDefect (cubeSet Q) a σ := by
      rw [traceDefect_eq_full_framedTrace,
        traceDefect_eq_full_framedTrace, hFrame]
      simp [frameMatrix, a]
    have hRaw : rawCubeFourLoadTrace M m Q t ω =
        traceDefect (cubeSet Q) a σ := rfl
    exact hTraceFrame.trans hRaw.symm
  have hMatrix := main_full_response_operator_norm_le_trace_bound Q
    (mul_pos (inv_pos.mpr hσ) M.nu_pos) hEllFrame
  change fullResponseOperatorNorm Q ((σ⁻¹ : ℝ) • a) ≤ _
  calc
    fullResponseOperatorNorm Q ((σ⁻¹ : ℝ) • a) ≤
        1 + 2 * traceDefect (cubeSet Q) ((σ⁻¹ : ℝ) • a) 1 +
          Real.sqrt (2 * traceDefect (cubeSet Q) ((σ⁻¹ : ℝ) • a) 1) := hMatrix
    _ = 1 + 2 * rawCubeFourLoadTrace M m Q t ω +
          Real.sqrt (2 * rawCubeFourLoadTrace M m Q t ω) := by rw [hTrace]

/-- The actual depth maximum of the OLD-frame trace variable, with the same
descendants and base cube as the source history. -/
noncomputable def mainPartialInsertedTraceDepthMax
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2) (j : ℕ) : ℝ :=
  (Inverse.historyFiniteMax (descendantsAtDepth (originCube 2 (m - 5)) j)
    (fun Q ω => ENNReal.ofReal (rawCubeFourLoadTrace M m Q t ω)) ω).toReal

/-- Every finite descendant trace maximum is finite on every cutoff sample. -/
theorem main_partial_inserted_trace_depth_max_ne_top
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2) (j : ℕ) :
    Inverse.historyFiniteMax (descendantsAtDepth (originCube 2 (m - 5)) j)
      (fun Q ω => ENNReal.ofReal (rawCubeFourLoadTrace M m Q t ω)) ω ≠ ⊤ := by
  classical
  unfold Inverse.historyFiniteMax
  apply ne_of_lt
  apply (Finset.sup_lt_iff (by simp : (⊥ : ℝ≥0∞) < ⊤)).mpr
  intro Q hQ
  exact ENNReal.ofReal_lt_top

/-- The source max-based ordinary history on the actual cutoff sample space.
This has the same ENNReal carrier as `mainOrdinaryTraceMaxHistory`. -/
noncomputable def mainPartialInsertedTraceMaxHistory
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2) : ℝ≥0∞ :=
  ENNReal.ofReal (1 - Scalar.inverseHistoryDiscount) *
    ∑' j : ℕ, ENNReal.ofReal (Scalar.inverseHistoryDiscount ^ j) *
      Inverse.historyFiniteMax (descendantsAtDepth (originCube 2 (m - 5)) j)
        (fun Q ω => ENNReal.ofReal (rawCubeFourLoadTrace M m Q t ω)) ω

/-- Finiteness of the actual max-based source history gives the real depth
series and identifies its normalized sum with the `toReal` carrier. -/
theorem main_partial_inserted_trace_history_real_series
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2)
    (hfinite : mainPartialInsertedTraceMaxHistory M m t ω < ⊤) :
    Summable (fun j : ℕ => Scalar.inverseHistoryDiscount ^ j *
      mainPartialInsertedTraceDepthMax M m t ω j) ∧
    (1 - Scalar.inverseHistoryDiscount) * ∑' j : ℕ,
      Scalar.inverseHistoryDiscount ^ j *
        mainPartialInsertedTraceDepthMax M m t ω j =
      (mainPartialInsertedTraceMaxHistory M m t ω).toReal := by
  let α := Scalar.inverseHistoryDiscount
  let c : ℝ≥0∞ := ENNReal.ofReal (1 - α)
  let F : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal (α ^ j) *
    Inverse.historyFiniteMax (descendantsAtDepth (originCube 2 (m - 5)) j)
      (fun Q ω => ENNReal.ofReal (rawCubeFourLoadTrace M m Q t ω)) ω
  have hα := Scalar.inverse_history_discount_range
  have hcPos : 0 < c := by
    dsimp [c]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hα.2)
  have hproduct : c * (∑' j : ℕ, F j) ≠ ⊤ := by
    simpa [c, F, α, mainPartialInsertedTraceMaxHistory] using
      (ne_of_lt hfinite)
  have hsumNe : (∑' j : ℕ, F j) ≠ ⊤ := by
    exact (ENNReal.lt_top_of_mul_ne_top_right hproduct (ne_of_gt hcPos)).ne
  have hSeriesENN : Summable (fun j : ℕ => (F j).toReal) :=
    ENNReal.summable_toReal hsumNe
  have hterm (j : ℕ) : (F j).toReal =
      α ^ j * mainPartialInsertedTraceDepthMax M m t ω j := by
    change (ENNReal.ofReal (α ^ j) *
      Inverse.historyFiniteMax (descendantsAtDepth (originCube 2 (m - 5)) j)
        (fun Q ω => ENNReal.ofReal (rawCubeFourLoadTrace M m Q t ω)) ω).toReal =
      α ^ j * mainPartialInsertedTraceDepthMax M m t ω j
    rw [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg hα.1.le j)]
    rfl
  have hSeriesReal : Summable (fun j : ℕ => α ^ j *
      mainPartialInsertedTraceDepthMax M m t ω j) := by
    apply hSeriesENN.congr
    intro j
    exact hterm j
  have hRealSum : (∑' j : ℕ, F j).toReal =
      ∑' j : ℕ, α ^ j * mainPartialInsertedTraceDepthMax M m t ω j := by
    rw [ENNReal.tsum_toReal_eq (fun j => ENNReal.ne_top_of_tsum_ne_top hsumNe j)]
    exact tsum_congr hterm
  have hHistoryReal : (mainPartialInsertedTraceMaxHistory M m t ω).toReal =
      (1 - α) * ∑' j : ℕ, α ^ j *
        mainPartialInsertedTraceDepthMax M m t ω j := by
    change (c * ∑' j : ℕ, F j).toReal = _
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_nonneg.mpr hα.2.le), hRealSum]
  refine ⟨?_, ?_⟩
  · simpa only [α] using hSeriesReal
  · rw [hHistoryReal]

/-- The actual depthwise matrix multiplier in the OLD frame. -/
noncomputable def mainPartialInsertedMultiplierDepthMax
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2) (j : ℕ) : ℝ :=
  Scalar.fullResponseDepthMax (originCube 2 (m - 5))
    ((Annealed.sigmaBar M m : ℝ)⁻¹ •
      (Model.partialInsertedCoefficient M m t ω).toFun) j

/-- The real value of the max-based full-response matrix history M_U. -/
noncomputable def mainPartialInsertedMultiplierHistory
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  (1 - Scalar.inverseHistoryDiscount) * ∑' j : ℕ,
    Scalar.inverseHistoryDiscount ^ j *
      mainPartialInsertedMultiplierDepthMax M m t ω j

/-- Each actual depthwise multiplier maximum is bounded by the corresponding
maximal trace depth. This is the finite-descendant consequence of the actual
coarse matrix estimate above; no matrix/history bound is assumed. -/
theorem main_partial_inserted_multiplier_depth_le_trace
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (ω : Cutoff.CutoffSample 2) (j : ℕ) :
    0 ≤ mainPartialInsertedMultiplierDepthMax M m t ω j ∧
      mainPartialInsertedMultiplierDepthMax M m t ω j ≤
        1 + 2 * mainPartialInsertedTraceDepthMax M m t ω j +
          Real.sqrt (2 * mainPartialInsertedTraceDepthMax M m t ω j) := by
  let Q : TriadicCube 2 := originCube 2 (m - 5)
  let s := descendantsAtDepth Q j
  let a : CoeffField 2 := (Annealed.sigmaBar M m : ℝ)⁻¹ •
    (Model.partialInsertedCoefficient M m t ω).toFun
  let T : ℝ := mainPartialInsertedTraceDepthMax M m t ω j
  have hT0 : 0 ≤ T := by
    dsimp [T, mainPartialInsertedTraceDepthMax]
    exact ENNReal.toReal_nonneg
  have hTcell (R : TriadicCube 2) (hR : R ∈ s) :
      rawCubeFourLoadTrace M m R t ω ≤ T := by
    have hmax := Finset.le_sup
      (f := fun R => ENNReal.ofReal (rawCubeFourLoadTrace M m R t ω)) hR
    have hreal := ENNReal.toReal_mono
      (main_partial_inserted_trace_depth_max_ne_top M m t ω j) hmax
    rw [ENNReal.toReal_ofReal
      (raw_cube_four_load_trace_nonneg M m R t ht ω)] at hreal
    simpa [T, mainPartialInsertedTraceDepthMax, s, Q, Inverse.historyFiniteMax] using hreal
  have hpoint (R : TriadicCube 2) (hR : R ∈ s) :
      fullResponseOperatorNorm R a ≤ 1 + 2 * T + Real.sqrt (2 * T) := by
    have hCell := main_partial_inserted_response_norm_le_raw_trace
      M m R t ht ω
    have htrace := hTcell R hR
    have hscaled : 2 * rawCubeFourLoadTrace M m R t ω ≤ 2 * T := by nlinarith
    have hroot := Real.sqrt_le_sqrt hscaled
    change fullResponseOperatorNorm R a ≤ _
    calc
      fullResponseOperatorNorm R a ≤
          1 + 2 * rawCubeFourLoadTrace M m R t ω +
            Real.sqrt (2 * rawCubeFourLoadTrace M m R t ω) := by
              simpa [a] using hCell
      _ ≤ 1 + 2 * T + Real.sqrt (2 * T) := by nlinarith
  have hmax := Book.Ch02.finsetSupReal_le s (descendantsAtDepth_nonempty Q j) hpoint
  constructor
  · exact Scalar.full_response_depth_max_nonneg Q a j
  · change Scalar.fullResponseDepthMax Q a j ≤ 1 + 2 * T + Real.sqrt (2 * T)
    exact hmax

/-- Nonnegativity of the actual max-based trace history at each depth. -/
theorem main_partial_inserted_trace_depth_nonneg
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (ω : Cutoff.CutoffSample 2) (j : ℕ) :
    0 ≤ mainPartialInsertedTraceDepthMax M m t ω j := by
  unfold mainPartialInsertedTraceDepthMax
  exact ENNReal.toReal_nonneg

/-- Jensen's inequality for the normalized geometric history.  The tail
weight `alpha^N` is assigned the value zero, so each finite prefix has total
mass one; passing through nonnegative partial sums proves the full series
estimate. -/
theorem main_weighted_root_history_le
    (alpha : ℝ) (hα0 : 0 ≤ alpha) (hα1 : alpha < 1)
    (T : ℕ → ℝ) (hT0 : ∀ j, 0 ≤ T j)
    (hTsum : Summable (fun j : ℕ => alpha ^ j * T j)) :
    Summable (fun j : ℕ => (1 - alpha) * alpha ^ j * Real.sqrt (2 * T j)) ∧
      (1 - alpha) * ∑' j : ℕ, alpha ^ j * Real.sqrt (2 * T j) ≤
        Real.sqrt (2 * ((1 - alpha) * ∑' j : ℕ, alpha ^ j * T j)) := by
  let w : ℕ → ℝ := fun j => (1 - alpha) * alpha ^ j
  let H : ℝ := (1 - alpha) * ∑' j : ℕ, alpha ^ j * T j
  have hαlt : 0 < 1 - alpha := sub_pos.mpr hα1
  have hw (j : ℕ) : 0 ≤ w j :=
    mul_nonneg (sub_nonneg.mpr hα1.le) (pow_nonneg hα0 j)
  have hWSeries : Summable w := by
    simpa only [w] using (summable_geometric_of_lt_one hα0 hα1).mul_left (1 - alpha)
  have hW (N : ℕ) : alpha ^ N + ∑ j ∈ Finset.range N, w j = 1 := by
    induction N with
    | zero => simp [w]
    | succ N ih =>
        calc
          alpha ^ (N + 1) + ∑ j ∈ Finset.range (N + 1), w j =
              alpha ^ N * alpha + (∑ j ∈ Finset.range N, w j) + w N := by
                rw [pow_succ, Finset.sum_range_succ]
                ring
          _ = alpha ^ N + ∑ j ∈ Finset.range N, w j := by
                simp only [w]
                ring
          _ = 1 := ih
  have hWeightedTSummable : Summable (fun j : ℕ => w j * T j) := by
    simpa only [w, mul_assoc] using hTsum.mul_left (1 - alpha)
  have hWeightedTsum : (∑' j : ℕ, w j * T j) = H := by
    dsimp [H]
    rw [show (fun j : ℕ => w j * T j) =
        fun j => (1 - alpha) * (alpha ^ j * T j) by
          funext j; simp [w, mul_assoc]]
    rw [tsum_mul_left]
  have hHnonneg : 0 ≤ H := by
    dsimp [H]
    exact mul_nonneg hαlt.le (tsum_nonneg fun j => mul_nonneg (pow_nonneg hα0 j) (hT0 j))
  have hPartial (N : ℕ) :
      (∑ j ∈ Finset.range N, w j * T j) ≤ H := by
    calc
      (∑ j ∈ Finset.range N, w j * T j) ≤ ∑' j : ℕ, w j * T j :=
        hWeightedTSummable.sum_le_tsum (Finset.range N) (fun j _ =>
          mul_nonneg (hw j) (hT0 j))
      _ = H := hWeightedTsum
  have hJensen (N : ℕ) :
      (∑ j ∈ Finset.range N, w j * Real.sqrt (2 * T j)) ≤ Real.sqrt (2 * H) := by
    have h := Real.strictConcaveOn_sqrt.concaveOn.map_add_sum_le
      (t := Finset.range N) (w := w) (p := fun j => 2 * T j)
      (v := alpha ^ N) (q := (0 : ℝ))
      (fun j _ => hw j) (hW N)
      (fun j _ => Set.mem_Ici.mpr (mul_nonneg (by norm_num) (hT0 j)))
      (pow_nonneg hα0 N) (Set.mem_Ici.mpr le_rfl)
    have hJensen' :
        (∑ j ∈ Finset.range N, w j * Real.sqrt (2 * T j)) ≤
          Real.sqrt (2 * (∑ j ∈ Finset.range N, w j * T j)) := by
      have h' :
          (∑ j ∈ Finset.range N, w j * Real.sqrt (2 * T j)) ≤
            Real.sqrt (∑ j ∈ Finset.range N, w j * (2 * T j)) := by
        simpa only [smul_eq_mul, Real.sqrt_zero, zero_mul, mul_zero, zero_add] using h
      have hsum :
          (∑ j ∈ Finset.range N, w j * (2 * T j)) =
            2 * (∑ j ∈ Finset.range N, w j * T j) := by
        calc
          (∑ j ∈ Finset.range N, w j * (2 * T j)) =
              ∑ j ∈ Finset.range N, 2 * (w j * T j) := by
                apply Finset.sum_congr rfl
                intro j hj
                ring
          _ = 2 * (∑ j ∈ Finset.range N, w j * T j) := by rw [Finset.mul_sum]
      rw [hsum] at h'
      exact h'
    exact hJensen'.trans (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
      (hPartial N) (by norm_num)))
  have hRootWeighted : Summable (fun j : ℕ => w j * Real.sqrt (2 * T j)) :=
    summable_of_sum_range_le
      (fun j => mul_nonneg (hw j) (Real.sqrt_nonneg _)) hJensen
  have hRootTsum := hRootWeighted.tsum_le_of_sum_range_le hJensen
  have hRootRewrite :
      (1 - alpha) * ∑' j : ℕ, alpha ^ j * Real.sqrt (2 * T j) =
        ∑' j : ℕ, w j * Real.sqrt (2 * T j) := by
    rw [show (fun j : ℕ => w j * Real.sqrt (2 * T j)) =
        fun j => (1 - alpha) * (alpha ^ j * Real.sqrt (2 * T j)) by
          funext j; simp [w, mul_assoc], tsum_mul_left]
  rw [hRootRewrite]
  exact ⟨by simpa only [w, mul_assoc] using hRootWeighted, hRootTsum⟩

/-- The depthwise source matrix inequality, averaged over the normalized
geometric history.  `hDepth` is the finite-cell maximum estimate; the actual
partial-insertion instance is proved below from the response matrix theorem. -/
theorem main_weighted_matrix_history_bound
    (alpha : ℝ) (hα0 : 0 ≤ alpha) (hα1 : alpha < 1)
    (M H : ℕ → ℝ) (hH0 : ∀ j, 0 ≤ H j)
    (hDepth : ∀ j, 0 ≤ M j ∧ M j ≤ 1 + 2 * H j + Real.sqrt (2 * H j))
    (hHsum : Summable (fun j : ℕ => alpha ^ j * H j)) :
    (1 - alpha) * ∑' j : ℕ, alpha ^ j * M j ≤
      1 + 2 * ((1 - alpha) * ∑' j : ℕ, alpha ^ j * H j) +
        Real.sqrt (2 * ((1 - alpha) * ∑' j : ℕ, alpha ^ j * H j)) := by
  let w : ℕ → ℝ := fun j => (1 - alpha) * alpha ^ j
  let Hbar : ℝ := (1 - alpha) * ∑' j : ℕ, alpha ^ j * H j
  have hαlt : 0 < 1 - alpha := sub_pos.mpr hα1
  have hw (j : ℕ) : 0 ≤ w j :=
    mul_nonneg (sub_nonneg.mpr hα1.le) (pow_nonneg hα0 j)
  have hWSeries : Summable w := by
    simpa only [w] using (summable_geometric_of_lt_one hα0 hα1).mul_left (1 - alpha)
  have hWtsum : (∑' j : ℕ, w j) = 1 := by
    dsimp [w]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hα0 hα1]
    field_simp [ne_of_gt hαlt]
  have hWeightedH : Summable (fun j : ℕ => w j * H j) := by
    simpa only [w, mul_assoc] using hHsum.mul_left (1 - alpha)
  have hWeightedHtsum : (∑' j : ℕ, w j * H j) = Hbar := by
    dsimp [Hbar]
    rw [show (fun j : ℕ => w j * H j) =
        fun j => (1 - alpha) * (alpha ^ j * H j) by
          funext j; simp [w, mul_assoc], tsum_mul_left]
  have hRoot := main_weighted_root_history_le alpha hα0 hα1 H hH0 hHsum
  have hRootWeighted : Summable (fun j : ℕ => w j * Real.sqrt (2 * H j)) := by
    simpa only [w, mul_assoc] using hRoot.1
  have hMajor : Summable (fun j : ℕ => w j * (1 + 2 * H j + Real.sqrt (2 * H j))) := by
    have hsum : Summable (fun j : ℕ => w j + (2 * (w j * H j) +
        w j * Real.sqrt (2 * H j))) :=
      hWSeries.add ((hWeightedH.mul_left 2).add hRootWeighted)
    apply hsum.congr
    intro j
    simp only [w]
    ring
  have hMweighted : Summable (fun j : ℕ => w j * M j) := by
    apply Summable.of_nonneg_of_le (fun j => mul_nonneg (hw j) (hDepth j).1)
      (fun j => mul_le_mul_of_nonneg_left (hDepth j).2 (hw j)) hMajor
  have hMsum := hMweighted.tsum_le_tsum
    (fun j => mul_le_mul_of_nonneg_left (hDepth j).2 (hw j)) hMajor
  have hHistory :
      ∑' j : ℕ, w j * (1 + 2 * H j + Real.sqrt (2 * H j)) ≤
        1 + 2 * Hbar + Real.sqrt (2 * Hbar) := by
    have hsplit :
        (fun j : ℕ => w j * (1 + 2 * H j + Real.sqrt (2 * H j))) =
          fun j => w j + (2 * (w j * H j) + w j * Real.sqrt (2 * H j)) := by
      funext j
      simp only [w]
      ring
    calc
      ∑' j : ℕ, w j * (1 + 2 * H j + Real.sqrt (2 * H j)) =
          ∑' j : ℕ, (w j + (2 * (w j * H j) + w j * Real.sqrt (2 * H j))) := by
            rw [hsplit]
      _ = (∑' j : ℕ, w j) +
            (∑' j : ℕ, (2 * (w j * H j) + w j * Real.sqrt (2 * H j))) :=
              hWSeries.tsum_add ((hWeightedH.mul_left 2).add hRootWeighted)
      _ = (∑' j : ℕ, w j) +
            ((∑' j : ℕ, (2 * (w j * H j))) +
              (∑' j : ℕ, w j * Real.sqrt (2 * H j))) := by
              rw [(hWeightedH.mul_left 2).tsum_add hRootWeighted]
      _ = 1 + 2 * Hbar + (∑' j : ℕ, w j * Real.sqrt (2 * H j)) := by
            have hDouble : (∑' j : ℕ, 2 * (w j * H j)) = 2 * Hbar := by
              rw [tsum_mul_left, hWeightedHtsum]
            rw [hWtsum, hDouble]
            ring
      _ ≤ 1 + 2 * Hbar + Real.sqrt (2 * Hbar) := by
            have hRootRewrite :
                (1 - alpha) * ∑' j : ℕ, alpha ^ j * Real.sqrt (2 * H j) =
                  ∑' j : ℕ, w j * Real.sqrt (2 * H j) := by
              rw [show (fun j : ℕ => w j * Real.sqrt (2 * H j)) =
                  fun j => (1 - alpha) * (alpha ^ j * Real.sqrt (2 * H j)) by
                    funext j; simp [w, mul_assoc], tsum_mul_left]
            have hRootBound :
                (∑' j : ℕ, w j * Real.sqrt (2 * H j)) ≤ Real.sqrt (2 * Hbar) := by
              calc
                (∑' j : ℕ, w j * Real.sqrt (2 * H j)) =
                    (1 - alpha) * ∑' j : ℕ, alpha ^ j * Real.sqrt (2 * H j) :=
                      hRootRewrite.symm
                _ ≤ Real.sqrt (2 * ((1 - alpha) * ∑' j : ℕ, alpha ^ j * H j)) := hRoot.2
                _ = Real.sqrt (2 * Hbar) := by rw [show
                    (1 - alpha) * ∑' j : ℕ, alpha ^ j * H j = Hbar by rfl]
            linarith
  have hMRewrite :
      (∑' j : ℕ, w j * M j) = (1 - alpha) * ∑' j : ℕ, alpha ^ j * M j := by
    rw [show (fun j : ℕ => w j * M j) =
        fun j => (1 - alpha) * (alpha ^ j * M j) by funext j; simp [w, mul_assoc],
      tsum_mul_left]
  rw [← hMRewrite]
  have hHbarEq : Hbar = (1 - alpha) * ∑' j : ℕ, alpha ^ j * H j := rfl
  rw [hHbarEq] at hHistory
  exact hMsum.trans hHistory

/-- Actual OLD-frame history aggregation for the partial insertion. The
per-depth matrix estimate is instantiated from actual trace defects above;
the only input is summability of the source's max-based trace rows. -/
theorem main_partial_inserted_weighted_multiplier_bound
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (ω : Cutoff.CutoffSample 2)
    (hTraceSum : Summable (fun j : ℕ =>
      Scalar.inverseHistoryDiscount ^ j *
        mainPartialInsertedTraceDepthMax M m t ω j)) :
    (1 - Scalar.inverseHistoryDiscount) * ∑' j : ℕ,
        Scalar.inverseHistoryDiscount ^ j *
          mainPartialInsertedMultiplierDepthMax M m t ω j ≤
      1 + 2 * ((1 - Scalar.inverseHistoryDiscount) * ∑' j : ℕ,
          Scalar.inverseHistoryDiscount ^ j *
            mainPartialInsertedTraceDepthMax M m t ω j) +
        Real.sqrt (2 * ((1 - Scalar.inverseHistoryDiscount) * ∑' j : ℕ,
          Scalar.inverseHistoryDiscount ^ j *
            mainPartialInsertedTraceDepthMax M m t ω j)) := by
  let Dm : ℕ → ℝ := mainPartialInsertedMultiplierDepthMax M m t ω
  let Dh : ℕ → ℝ := mainPartialInsertedTraceDepthMax M m t ω
  have hα := Scalar.inverse_history_discount_range
  have hDepth (j : ℕ) :
      0 ≤ Dm j ∧ Dm j ≤ 1 + 2 * Dh j + Real.sqrt (2 * Dh j) := by
    simpa only [Dm, Dh] using
      main_partial_inserted_multiplier_depth_le_trace M m t ht ω j
  have hHnonneg (j : ℕ) : 0 ≤ Dh j := by
    simpa only [Dh] using main_partial_inserted_trace_depth_nonneg M m t ht ω j
  have h := main_weighted_matrix_history_bound Scalar.inverseHistoryDiscount
    hα.1.le hα.2 Dm Dh hHnonneg hDepth hTraceSum
  simpa only [Dm, Dh] using h

/-- Pathwise source matrix moment inequality for the actual cutoff-sample
history. Its only input is finiteness of the actual max-based trace history;
the cell matrix estimate and its normalized geometric summation are proved
internally above. -/
theorem main_partial_inserted_multiplier_le_trace_history
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (ω : Cutoff.CutoffSample 2)
    (hfinite : mainPartialInsertedTraceMaxHistory M m t ω < ⊤) :
    mainPartialInsertedMultiplierHistory M m t ω ≤
      1 + 2 * (mainPartialInsertedTraceMaxHistory M m t ω).toReal +
        Real.sqrt (2 * (mainPartialInsertedTraceMaxHistory M m t ω).toReal) := by
  have hTrace := main_partial_inserted_trace_history_real_series M m t ω hfinite
  have hWeighted := main_partial_inserted_weighted_multiplier_bound
    M m t ht ω hTrace.1
  change (1 - Scalar.inverseHistoryDiscount) * ∑' j : ℕ,
      Scalar.inverseHistoryDiscount ^ j *
        mainPartialInsertedMultiplierDepthMax M m t ω j ≤ _
  calc
    _ ≤ 1 + 2 * ((1 - Scalar.inverseHistoryDiscount) * ∑' j : ℕ,
          Scalar.inverseHistoryDiscount ^ j *
            mainPartialInsertedTraceDepthMax M m t ω j) +
        Real.sqrt (2 * ((1 - Scalar.inverseHistoryDiscount) * ∑' j : ℕ,
          Scalar.inverseHistoryDiscount ^ j *
            mainPartialInsertedTraceDepthMax M m t ω j)) := hWeighted
    _ = 1 + 2 * (mainPartialInsertedTraceMaxHistory M m t ω).toReal +
        Real.sqrt (2 * (mainPartialInsertedTraceMaxHistory M m t ω).toReal) := by
          rw [hTrace.2]

theorem main_partial_inserted_multiplier_history_nonneg
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    0 ≤ mainPartialInsertedMultiplierHistory M m t ω := by
  have hα := Scalar.inverse_history_discount_range
  unfold mainPartialInsertedMultiplierHistory
  apply mul_nonneg (sub_nonneg.mpr hα.2.le)
  apply tsum_nonneg
  intro j
  exact mul_nonneg (pow_nonneg hα.1.le j)
    (Scalar.full_response_depth_max_nonneg (originCube 2 (m - 5))
      ((Annealed.sigmaBar M m : ℝ)⁻¹ •
        (Model.partialInsertedCoefficient M m t ω).toFun) j)

end ASDExplicitGamma.Main
