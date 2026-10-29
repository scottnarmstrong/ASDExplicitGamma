module

public import ASDExplicitGamma.Inverse.FullResponseActiveMeanBridge
public import ASDExplicitGamma.Inverse.FullResponseActiveTriangle
public import ASDExplicitGamma.Inverse.HybridFullTraceCongruence
public import ASDExplicitGamma.Inverse.HybridFrameComparison
public import ASDExplicitGamma.Inverse.FullResponseSharpCongruence

/-! The exact active trace coefficients in the observer frame. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider Algsuperdiff.Section3.Provider.Whitney
open Algsuperdiff.Section3.Provider.Multiscale
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic ASDExplicitGamma.Response
open ASDExplicitGamma.Variational
open scoped ENNReal

noncomputable section

/-- The constant active trace coefficient c₀ₜ of the source. -/
def fullResponseTraceC0 : ℝ :=
  2 * (1 + Real.sqrt 2 * (10 * waveGateEta .full))^2 *
    (1 + 6 * rootTau .full)

/-- The active wave coefficient c₁ₜ of the source. -/
def fullResponseTraceC1 : ℝ := 2 * (1 + 6 * rootTau .full)

/-- The later-band mean on the actual Whitney parent in its own completed frame. -/
def fullResponseParentWaveMean (M : ABKModel 2) (P : TriadicCube 2)
    (m J : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  cubeAverage P
    (laterBandW2 P (P.scale+40) J (sourceBandWeights m weights) ω).value.toFun /
      (Annealed.sigmaBar M (P.scale+40) : ℝ)

/-- The exact source active trace cap after transforming the four loads.
The factor four cancels the normalized full trace's final division by four. -/
theorem good_parent_active_triangle_transformed_full_trace_sharp_root_mean
    (M : ABKModel 2) {Q U : TriadicCube 2} {a : ℕ}
    (hU : U ∈ descendantsAtDepth Q a) (ha : a ≤ 2)
    (pi : Equiv.Perm (Fin 2)) (m J : ℤ) (hn : Q.scale+40 ≤ m)
    (hm : m ≤ J) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (ω : Cutoff.CutoffSample 2)
    (hgood : ω ∉ cellFailure M (rootTau .full) (waveGateEta .full) Q)
    (C : Mat 2) :
    ENNReal.ofReal (∑ j : Fin 2 × Bool,
      hybridFullTraceCellLoadEnergy (Annealed.sigmaBar M (Q.scale+40) : ℝ)
        (coarseBlockMatrix (Whitney.KuhnCell.mk U pi).openCarrier
          (attenuatedCoefficient M m J weights ω)) C j) ≤
      ENNReal.ofReal (4 * ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) C‖^2) *
        ENNReal.ofReal (rootEdelta .full * (fullResponseTraceC0 +
          fullResponseTraceC1 * (fullResponseParentWaveMean M Q m J weights ω)^2)) := by
  classical
  let n := Q.scale+40
  let σ := (Annealed.sigmaBar M n : ℝ)
  let A := coarseBlockMatrix (Whitney.KuhnCell.mk U pi).openCarrier
    (attenuatedCoefficient M m J weights ω)
  let k := oldResponseCoefficient Q n ω +
    laterResponseCoefficient Q n J (sourceBandWeights m weights) ω
  let aQ := sensitivityBookCoeffOn Q M.nu M.nu_pos k
  let T := kuhnCellDomain (Whitney.KuhnCell.mk U pi)
  have hT : (T : Set (Vec 2)) ⊆ openCubeSet Q :=
    (Whitney.KuhnCell.openCarrier_subset_openCubeSet _).trans
      (openCubeSet_subset_of_mem_descendantsAtDepth hU)
  let aT := restrictCoeffOn aQ hT
  have hBook : Book.Ch02.coarseBlockMatrix T aT = A := by
    simpa only [A, aT, aQ, k, n, T, kuhnCellDomain] using
      attenuated_domain_matrix_eq M Q n m J hn hm weights ω T hT
  have hsym : IsSymmetricBlockMat A := by
    rw [← hBook]
    exact Book.Ch02.isSymmetricBlockMat_coarseBlockMatrix T aT
  have hquad (P : BlockVec 2) : 0 ≤ blockVecDot P (blockMatVecMul A P) := by
    by_cases hP : P = 0
    · rw [hP]
      simp [blockVecDot, blockMatVecMul, vecDot, matVecMul]
    · rw [← hBook]
      exact (Book.Ch02.blockCoarseMatrixTheory T aT).block_matrix_posDef P hP |>.le
  have hUL : A.upperLeft.PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · have hHerm : A.upperLeft.IsHermitian := by
        ext i j
        have hh := hsym (Sum.inl j) (Sum.inl i)
        change A.upperLeft j i = A.upperLeft i j at hh
        simpa [Matrix.conjTranspose_apply, star_trivial] using hh
      simpa [Matrix.IsHermitian, Matrix.IsSymm] using hHerm
    · intro p
      simpa [blockVecDot, blockMatVecMul, vecDot, matVecMul,
        Matrix.mulVec, Fin.sum_univ_two] using hquad (p, 0)
  have hLR : A.lowerRight.PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · have hHerm : A.lowerRight.IsHermitian := by
        ext i j
        have hh := hsym (Sum.inr j) (Sum.inr i)
        change A.lowerRight j i = A.lowerRight i j at hh
        simpa [Matrix.conjTranspose_apply, star_trivial] using hh
      simpa [Matrix.IsHermitian, Matrix.IsSymm] using hHerm
    · intro q
      simpa [blockVecDot, blockMatVecMul, vecDot, matVecMul,
        Matrix.mulVec, Fin.sum_univ_two] using hquad (0, q)
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M n).1
  have hloads := hybrid_full_trace_cell_load_sum_sharp_le σ A C hσ hUL hLR
  let F := 4 * ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) C‖^2
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hreal : (∑ j : Fin 2 × Bool, hybridFullTraceCellLoadEnergy σ A C j) ≤
      F * (Matrix.trace (toFullBlockMat (frameMatrix σ A))/4) :=
    hloads.trans_eq (by dsimp only [F]; ring)
  have hcap := good_parent_active_triangle_actual_full_trace_root_mean
    M hU ha pi m J hn hm weights hw ω hgood
  apply (ENNReal.ofReal_le_ofReal hreal).trans
  rw [ENNReal.ofReal_mul hF]
  apply mul_le_mul_of_nonneg_left _ bot_le
  simpa only [fullResponseTraceC0, fullResponseTraceC1,
    fullResponseParentWaveMean, A, σ, n] using hcap

end
end ASDExplicitGamma.Inverse
