module

public import ASDExplicitGamma.Inverse.AssemblyReferenceEnergy
public import ASDExplicitGamma.Inverse.FullResponseActiveTriangle
public import ASDExplicitGamma.Inverse.HybridFullTraceCongruence
public import ASDExplicitGamma.Inverse.HybridFrameComparison

/-! Transformed four-load payments in the source root frame. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider Algsuperdiff.Section3.Provider.Whitney
open Algsuperdiff.Section3.Provider.Multiscale
open ASDExplicitGamma.Triadic ASDExplicitGamma.Response ASDExplicitGamma.Variational
open scoped ENNReal Matrix.Norms.Elementwise
noncomputable section

/-- The transformed four-load sum on an actual active hybrid simplex, viewed
in the observer frame, is at most the exact parent-frame load sum times the
root-gap and selected-layer clock. -/
theorem assembly_active_load_sum_root_frame_le
    (M : ABKModel 2) (Q : TriadicCube 2) (H : ℕ) (k : ℕ)
    (hH : heightEntrance k ≤ H) (ω : Cutoff.CutoffSample 2)
    (J : ℤ) (hmJ : protectedOldLabel Q.scale k ≤ J)
    (weights : ℤ → ℝ)
    (C : HybridCell Q H (rootBadWhitneyCells M Q H resetAllOrderTau
      (ASDExplicitGamma.Gaussian.waveGateEta .allOrder) ω) → Mat 2)
    (i : HybridActiveCell Q H (rootBadWhitneyCells M Q H resetAllOrderTau
      (ASDExplicitGamma.Gaussian.waveGateEta .allOrder) ω)) :
    let U := (hybridParent (.inr i)).2.val
    let n := U.scale + 40
    let σ := (Annealed.sigmaBar M (Q.scale-1) : ℝ)
    let σold := (Annealed.sigmaBar M n : ℝ)
    let G := rootAssemblyClock M.gamma H (hybridParent (.inr i)).1
    ENNReal.ofReal (∑ j : Fin 2 × Bool,
      hybridFullTraceCellLoadEnergy σ
        (coarseBlockMatrix (hybridDomain (.inr i) : Set (Vec 2))
          (attenuatedCoefficient M (protectedOldLabel Q.scale k) J weights ω)) (C (.inr i)) j) ≤
      ENNReal.ofReal G * ENNReal.ofReal (∑ j : Fin 2 × Bool,
        hybridFullTraceCellLoadEnergy σold
          (coarseBlockMatrix (hybridDomain (.inr i) : Set (Vec 2))
            (attenuatedCoefficient M (protectedOldLabel Q.scale k) J weights ω)) (C (.inr i)) j) := by
  classical
  dsimp only
  let S := rootBadWhitneyCells M Q H resetAllOrderTau
    (ASDExplicitGamma.Gaussian.waveGateEta .allOrder) ω
  let V := hybridParent (.inr i)
  let P := V.2.val
  let n := P.scale + 40
  let σ := (Annealed.sigmaBar M (Q.scale-1) : ℝ)
  let σold := (Annealed.sigmaBar M n : ℝ)
  let T := hybridDomain (.inr i)
  let aP := sensitivityBookCoeffOn P M.nu M.nu_pos
    (oldResponseCoefficient P n ω +
      laterResponseCoefficient P n J (sourceBandWeights (protectedOldLabel Q.scale k) weights) ω)
  let aT := restrictCoeffOn aP (hybrid_domain_subset_parent (.inr i))
  let A := coarseBlockMatrix (hybridDomain (.inr i) : Set (Vec 2))
    (attenuatedCoefficient M (protectedOldLabel Q.scale k) J weights ω)
  let D := planarFluxMatrix (C (.inr i))
  let A' : BlockMat 2 :=
    { upperLeft := (C (.inr i)).transpose * A.upperLeft * (C (.inr i))
      upperRight := (C (.inr i)).transpose * A.upperRight * D
      lowerLeft := D.transpose * A.lowerLeft * (C (.inr i))
      lowerRight := D.transpose * A.lowerRight * D }
  let G := rootAssemblyClock M.gamma H V.1
  have h333 : 333 ≤ H := by unfold heightEntrance at hH; omega
  have hPmem : P ∈ whitneyRootLayer Q H V.1 := V.2.property
  have hnpos : 1 ≤ V.1 := root_whitney_layer_pos Q H V.1 hPmem
  have hlabel : layerOldCutoff Q.scale H V.1=n :=
    root_whitney_old_cutoff_eq Q H V.1 hPmem
  have hn : n ≤ protectedOldLabel Q.scale k := by
    rw [← hlabel]
    exact layer_old_cutoff_le_protected Q.scale k H V.1 hH hnpos
  have hnref : n ≤ Q.scale-1 := by
    have hh := layer_old_cutoff_le_protected Q.scale k H V.1 hH hnpos
    rw [hlabel] at hh
    unfold protectedOldLabel at hh
    omega
  have hσold : 0 < σold := (Annealed.sigmaBar_characterization M n).1
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M (Q.scale-1)).1
  have hframe := assembly_layer_root_frame_ratio M Q.scale k H V.1 hH hnpos
  rw [hlabel] at hframe
  have hcontinuity := ASDExplicitGamma.Scalar.sigmaBar_structural_continuity
    M n (Q.scale-1-n) (by omega)
  have hcontinuity' : 1 ≤ σ/σold ∧ σ/σold ≤
      Real.rpow 3 (2*M.gamma*((Q.scale-1-n:ℤ):ℝ)) := by
    simpa only [σ, σold, n, P, V, show n+(Q.scale-1-n)=Q.scale-1 by omega] using hcontinuity
  have hratio : σ/σold ≤ G := by simpa only [σ, σold, n, P, V] using hframe
  have hholdle : σold ≤ σ := by
    have hh := (le_div_iff₀ hσold).mp hcontinuity'.1
    simpa [σ, σold] using hh
  have hG : 1 ≤ G := hcontinuity'.1.trans hratio
  have hT : (T : Set (Vec 2)) ⊆ openCubeSet P := by
    exact hybrid_domain_subset_parent (.inr i)
  have hBook : Book.Ch02.coarseBlockMatrix T aT = A := by
    simpa only [A, S, V, P, n] using
      attenuated_domain_matrix_eq M P n (protectedOldLabel Q.scale k) J hn hmJ weights ω
        T hT
  have hsym : IsSymmetricBlockMat A := by
    rw [← hBook]
    exact Book.Ch02.isSymmetricBlockMat_coarseBlockMatrix _ _
  have hquad (X : BlockVec 2) : 0 ≤ blockVecDot X (blockMatVecMul A X) := by
    by_cases hX : X = 0
    · rw [hX]
      simp [blockVecDot, blockMatVecMul, vecDot, matVecMul]
    · rw [← hBook]
      exact (Book.Ch02.blockCoarseMatrixTheory T aT).block_matrix_posDef X hX |>.le
  have hUL : A.upperLeft.PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · have hHerm : A.upperLeft.IsHermitian := by
        ext j k
        have hh := hsym (Sum.inl k) (Sum.inl j)
        change A.upperLeft k j = A.upperLeft j k at hh
        simpa [Matrix.conjTranspose_apply, star_trivial] using hh
      simpa [Matrix.IsHermitian, Matrix.IsSymm] using hHerm
    · intro p
      have hp := hquad (p, 0)
      simpa [blockVecDot, blockMatVecMul, vecDot, matVecMul,
        Matrix.mulVec, Fin.sum_univ_two] using hp
  have hLR : A.lowerRight.PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · have hHerm : A.lowerRight.IsHermitian := by
        ext j k
        have hh := hsym (Sum.inr k) (Sum.inr j)
        change A.lowerRight k j = A.lowerRight j k at hh
        simpa [Matrix.conjTranspose_apply, star_trivial] using hh
      simpa [Matrix.IsHermitian, Matrix.IsSymm] using hHerm
    · intro q
      have hq := hquad (0, q)
      simpa [blockVecDot, blockMatVecMul, vecDot, matVecMul,
        Matrix.mulVec, Fin.sum_univ_two] using hq
  have hUL' : A'.upperLeft.PosSemidef := by
    simpa [A', D] using
      hUL.conjTranspose_mul_mul_same (C (.inr i))
  have hLR' : A'.lowerRight.PosSemidef := by
    simpa [A', D] using
      hLR.conjTranspose_mul_mul_same D
  have hsum (s : ℝ) (hs : 0 < s) :
      (∑ j : Fin 2 × Bool, hybridFullTraceCellLoadEnergy s A (C (.inr i)) j) =
        Matrix.trace (toFullBlockMat (frameMatrix s A')) := by
    rw [hybrid_full_trace_cell_load_sum_eq s A (C (.inr i)) hs]
    simp [A', D, frameMatrix,
      toFullBlockMat, Matrix.trace, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.diag_apply]
    ring
  have hframeTrace := full_response_framed_trace_le_of_scalar_frame_growth
    A' σold σ G hσold hholdle hG hratio hUL'.trace_nonneg hLR'.trace_nonneg
  have hrootReal :
      (∑ j : Fin 2 × Bool, hybridFullTraceCellLoadEnergy σ A (C (.inr i)) j) ≤
        G * (∑ j : Fin 2 × Bool,
          hybridFullTraceCellLoadEnergy σold A (C (.inr i)) j) := by
    rw [hsum σ hσ, hsum σold hσold]
    exact hframeTrace
  have hG0 : 0 ≤ G := le_trans (by norm_num : (0:ℝ) ≤ 1) hG
  calc
    _ ≤ ENNReal.ofReal (G *
        (∑ j : Fin 2 × Bool,
          hybridFullTraceCellLoadEnergy σold A (C (.inr i)) j)) :=
      ENNReal.ofReal_le_ofReal hrootReal
    _ = ENNReal.ofReal G * ENNReal.ofReal
        (∑ j : Fin 2 × Bool,
          hybridFullTraceCellLoadEnergy σold A (C (.inr i)) j) :=
      ENNReal.ofReal_mul hG0

end
end ASDExplicitGamma.Inverse
