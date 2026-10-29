module

public import ASDExplicitGamma.Cold.PositiveTraceNorm
public import ASDExplicitGamma.Cold.PlateauGram
public import ASDExplicitGamma.Statements.TraceDefect

/-! # The actual symmetrized response defect is bounded by the full trace defect -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Matrix
open ASDExplicitGamma.Triadic
open scoped BigOperators RealInnerProductSpace
namespace ASDExplicitGamma.Cold

/-- The source bound `η_V ≤ T(V)` for the actual square response, derived internally. -/
theorem coarse_square_gram_defect_le_trace (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    matrixGramDefect (toFullBlockMat (coarseBlockMatrix (openCubeSet Q) a)) coarseGramSwap ≤
      traceDefect (openCubeSet Q) a 1 := by
  let A := toFullBlockMat (coarseBlockMatrix (openCubeSet Q) a)
  let R := coarseGramSwap
  let B := (1/2 : ℝ) • (A+R*A*R)-1
  let H := gramSymmetrizedDefect
    ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := BlockCoord 2)) A)
    ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := BlockCoord 2)) R)
  have hA : A.IsHermitian := coarse_square_full_isHermitian Q hEll
  have hR : R.IsHermitian := coarseGramSwap_isHermitian
  have hRR : R*R = 1 := coarseGramSwap_sq
  have hBAB : (R*A*R).IsHermitian := by
    have h := Matrix.isHermitian_conjTranspose_mul_mul R hA
    simpa only [hR.eq] using h
  have hB : B.IsHermitian := ((hA.add hBAB).smul (show IsSelfAdjoint (1/2 : ℝ) by simp)).sub
    Matrix.isHermitian_one
  have hH : H = (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := BlockCoord 2)) B := by
    dsimp [H,B,gramSymmetrizedDefect]
    simp only [map_sub,map_smul,map_add,map_mul,map_one]
    rfl
  have hSym : H.toLinearMap.IsSymmetric := by
    rw [hH,Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr hB
  have hPos (x : EuclideanSpace ℝ (BlockCoord 2)) : 0 ≤ ⟪x,H x⟫ :=
    gramSymmetrizedDefect_nonneg _ _
      (Matrix.isSymmetric_toEuclideanLin_iff.mpr coarseGramSwap_isHermitian)
      coarseGramSwap_involutive (fun y => (coarse_square_gram_signs Q hEll y).1)
      (fun y => (coarse_square_gram_signs Q hEll y).2) x
  have h := norm_le_trace_of_positive_operator H hSym hPos
  have htrace : LinearMap.trace ℝ (EuclideanSpace ℝ (BlockCoord 2)) H.toLinearMap = B.trace := by
    rw [hH,Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,trace_toEuclideanLin]
  rw [htrace] at h
  have hBt : B.trace = A.trace-4 := by
    dsimp [B]
    rw [Matrix.trace_sub,Matrix.trace_smul,Matrix.trace_add,
      Matrix.trace_mul_cycle,hRR,Matrix.one_mul,Matrix.trace_one]
    norm_num [Fintype.card_sum,Fintype.card_fin,smul_eq_mul]
    ring
  have hAt : A.trace-4 = traceDefect (openCubeSet Q) a 1 := by
    simp only [A,traceDefect,inv_one,one_mul,Matrix.trace,Matrix.diag_apply,
      Fintype.sum_sum_type,toFullBlockMat]
  rw [hBt,hAt] at h
  exact h

/-- Nonnegativity of the full normalized source trace defect also follows from this bound. -/
theorem coarse_square_traceDefect_nonneg (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) : 0 ≤ traceDefect (openCubeSet Q) a 1 :=
  (norm_nonneg _).trans (coarse_square_gram_defect_le_trace Q hEll)

/-- The source trace form of P3 now has no separate defect-comparison premise. -/
theorem plateau_gram_trace (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam η : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (hη : 0 < η)
    (w : AHarmonicFunction a (openCubeSet Q)) :
    blockVecDot (coarseGraphMean Q w) (coarseGraphMean Q w) ≤
      (2*(1+η)+(2+1/(4*η))*traceDefect (openCubeSet Q) a 1) *
      volumeAverage (openCubeSet Q) (scalarVariationEnergyIntegrand a w) :=
  plateau_gram_of_defect_le Q hEll hη (coarse_square_gram_defect_le_trace Q hEll) w

end ASDExplicitGamma.Cold
