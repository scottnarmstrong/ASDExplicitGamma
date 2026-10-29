module

public import ASDExplicitGamma.Inverse.AssemblyActiveMean
public import ASDExplicitGamma.Inverse.FullResponseActiveTriangle
public import ASDExplicitGamma.Inverse.HybridFullTraceCongruence

/-! The common slope's exact operator-norm payment on actual active triangles. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider Algsuperdiff.Section3.Provider.Multiscale
open ASDExplicitGamma.Triadic ASDExplicitGamma.Response ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian
open scoped ENNReal Matrix.Norms.Elementwise
noncomputable section

/-- A transformed active triangle is paid by its parent wave mean and the
squared operator norm of the common slope; every local mean premise is discharged. -/
theorem assembly_active_triangle_transformed_trace (M : ABKModel 2)
    {Q U : TriadicCube 2} {a : ℕ} (hU : U ∈ descendantsAtDepth Q a) (ha : a ≤ 2)
    (pi : Equiv.Perm (Fin 2)) (m J : ℤ) (hn : Q.scale+40 ≤ m) (hm : m ≤ J)
    (weights : ℤ → ℝ) (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (ω : Cutoff.CutoffSample 2)
    (hgood : ω ∉ cellFailure M resetAllOrderTau (waveGateEta .allOrder) Q) (C : Mat 2) :
    let n := Q.scale+40
    let σ := (Annealed.sigmaBar M n:ℝ)
    let h := laterBandW2 Q n J (sourceBandWeights m weights) ω
    let W := |cubeAverage Q h.value.toFun/σ|+2*(10*waveGateEta .allOrder)
    let A := coarseBlockMatrix (Whitney.KuhnCell.mk U pi).openCarrier
      (attenuatedCoefficient M m J weights ω)
    ENNReal.ofReal (∑ j : Fin 2 × Bool, hybridFullTraceCellLoadEnergy σ A C j) ≤
      ENNReal.ofReal (8*‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) C‖^2)*
        ENNReal.ofReal (2*rootAssemblySensitivity*(1+W^2)*(1+2*Real.sqrt 3*resetAllOrderTau)) := by
  classical
  dsimp only
  let n := Q.scale + 40
  let σ := (Annealed.sigmaBar M n : ℝ)
  let A := coarseBlockMatrix (Whitney.KuhnCell.mk U pi).openCarrier
    (attenuatedCoefficient M m J weights ω)
  let k := oldResponseCoefficient Q n ω +
    laterResponseCoefficient Q n J (sourceBandWeights m weights) ω
  let aQ := sensitivityBookCoeffOn Q M.nu M.nu_pos k
  let T := kuhnCellDomain (Whitney.KuhnCell.mk U pi)
  have hT : (T : Set (Vec 2)) ⊆ openCubeSet Q := by
    exact (Whitney.KuhnCell.openCarrier_subset_openCubeSet _).trans
      (openCubeSet_subset_of_mem_descendantsAtDepth hU)
  let aT := restrictCoeffOn aQ hT
  have hBook : Book.Ch02.coarseBlockMatrix T aT = A := by
    simpa only [A, aT, aQ, k, n, T, kuhnCellDomain] using
      attenuated_domain_matrix_eq M Q n m J hn hm weights ω T hT
  have hsym : IsSymmetricBlockMat A := by
    rw [← hBook]
    exact Book.Ch02.isSymmetricBlockMat_coarseBlockMatrix T aT
  have hquad (P : BlockVec 2) :
      0 ≤ blockVecDot P (blockMatVecMul A P) := by
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
      have hp := hquad (p, 0)
      simpa [blockVecDot, blockMatVecMul, vecDot, matVecMul,
        Matrix.mulVec, Fin.sum_univ_two] using hp
  have hLR : A.lowerRight.PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · have hHerm : A.lowerRight.IsHermitian := by
        ext i j
        have hh := hsym (Sum.inr j) (Sum.inr i)
        change A.lowerRight j i = A.lowerRight i j at hh
        simpa [Matrix.conjTranspose_apply, star_trivial] using hh
      simpa [Matrix.IsHermitian, Matrix.IsSymm] using hHerm
    · intro q
      have hq := hquad (0, q)
      simpa [blockVecDot, blockMatVecMul, vecDot, matVecMul,
        Matrix.mulVec, Fin.sum_univ_two] using hq
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M n).1
  have hloads := hybrid_full_trace_cell_load_sum_le σ A C hσ hUL hLR
  let F := 8 * ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) C‖^2
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hreal : (∑ j : Fin 2 × Bool,
      hybridFullTraceCellLoadEnergy σ A C j) ≤ F *
        (Matrix.trace (toFullBlockMat (frameMatrix σ A)) / 4) := by
    calc
      _ ≤ (2 * ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) C‖^2) *
          Matrix.trace (toFullBlockMat (frameMatrix σ A)) := hloads
      _ = F * (Matrix.trace (toFullBlockMat (frameMatrix σ A)) / 4) := by
        dsimp only [F]
        ring
  have htriangle := assembly_active_triangle_trace_parent_mean M hU ha pi m J hn hm weights hw ω hgood
  apply (ENNReal.ofReal_le_ofReal (by simpa only [A,σ,n] using hreal)).trans
  rw [ENNReal.ofReal_mul hF]
  exact mul_le_mul_of_nonneg_left htriangle bot_le

end
end ASDExplicitGamma.Inverse
