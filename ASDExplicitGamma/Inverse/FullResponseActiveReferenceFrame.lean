module

public import ASDExplicitGamma.Inverse.AssemblyReferenceEnergy
public import ASDExplicitGamma.Inverse.FullResponseActiveObserverMean
public import ASDExplicitGamma.Inverse.FullResponseActiveTriangle
public import ASDExplicitGamma.Inverse.HybridFullTraceCongruence
public import ASDExplicitGamma.Inverse.HybridFrameComparison

/-! Full-response transformed four-load payments in the source root frame. -/

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
theorem full_response_cell_load_sum_reference_frame_le
    (M : ABKModel 2) (Q : TriadicCube 2) (H : ℕ)
    (hH : 377 ≤ H) (ω : Cutoff.CutoffSample 2)
    (J : ℤ) (hmJ : Q.scale-342 ≤ J)
    (weights : ℤ → ℝ)
    (C : HybridCell Q H (rootBadWhitneyCells M Q H (rootTau .full)
      (ASDExplicitGamma.Gaussian.waveGateEta .full) ω) → Mat 2)
    (i : HybridCell Q H (rootBadWhitneyCells M Q H (rootTau .full)
      (ASDExplicitGamma.Gaussian.waveGateEta .full) ω)) :
    let U := (hybridParent i).2.val
    let n := U.scale + 40
    let σ := (Annealed.sigmaBar M (Q.scale-1) : ℝ)
    let σold := (Annealed.sigmaBar M n : ℝ)
    let G := rootAssemblyClock M.gamma H (hybridParent i).1
    ENNReal.ofReal (∑ j : Fin 2 × Bool,
      hybridFullTraceCellLoadEnergy σ
        (coarseBlockMatrix (hybridDomain i : Set (Vec 2))
          (attenuatedCoefficient M (Q.scale-342) J weights ω)) (C i) j) ≤
      ENNReal.ofReal G * ENNReal.ofReal (∑ j : Fin 2 × Bool,
        hybridFullTraceCellLoadEnergy σold
          (coarseBlockMatrix (hybridDomain i : Set (Vec 2))
            (attenuatedCoefficient M (Q.scale-342) J weights ω)) (C i) j) := by
  classical
  dsimp only
  let S := rootBadWhitneyCells M Q H (rootTau .full)
    (ASDExplicitGamma.Gaussian.waveGateEta .full) ω
  let V := hybridParent i
  let P := V.2.val
  let n := P.scale + 40
  let σ := (Annealed.sigmaBar M (Q.scale-1) : ℝ)
  let σold := (Annealed.sigmaBar M n : ℝ)
  let T := hybridDomain i
  let aP := sensitivityBookCoeffOn P M.nu M.nu_pos
    (oldResponseCoefficient P n ω +
      laterResponseCoefficient P n J (sourceBandWeights (Q.scale-342) weights) ω)
  let aT := restrictCoeffOn aP (hybrid_domain_subset_parent i)
  let A := coarseBlockMatrix (hybridDomain i : Set (Vec 2))
    (attenuatedCoefficient M (Q.scale-342) J weights ω)
  let D := planarFluxMatrix (C i)
  let A' : BlockMat 2 :=
    { upperLeft := (C i).transpose * A.upperLeft * (C i)
      upperRight := (C i).transpose * A.upperRight * D
      lowerLeft := D.transpose * A.lowerLeft * (C i)
      lowerRight := D.transpose * A.lowerRight * D }
  let G := rootAssemblyClock M.gamma H V.1
  have h333 : 333 ≤ H := by omega
  have hPmem : P ∈ whitneyRootLayer Q H V.1 := V.2.property
  have hnpos : 1 ≤ V.1 := root_whitney_layer_pos Q H V.1 hPmem
  have hlabel : layerOldCutoff Q.scale H V.1=n :=
    root_whitney_old_cutoff_eq Q H V.1 hPmem
  have hn : n ≤ Q.scale-342 := by
    rw [← hlabel]
    simpa only [protectedOldLabel, Nat.cast_zero, mul_zero, sub_zero] using
      layer_old_cutoff_le_protected Q.scale 0 H V.1
        (by simpa only [heightEntrance, mul_zero, add_zero] using hH) hnpos
  have hnref : n ≤ Q.scale-1 := by
    have hh := layer_old_cutoff_le_protected Q.scale 0 H V.1 (by simpa only [heightEntrance, mul_zero, add_zero] using hH) hnpos
    rw [hlabel] at hh
    unfold protectedOldLabel at hh
    omega
  have hσold : 0 < σold := (Annealed.sigmaBar_characterization M n).1
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M (Q.scale-1)).1
  have hframe := assembly_layer_root_frame_ratio M Q.scale 0 H V.1 (by simpa only [heightEntrance, mul_zero, add_zero] using hH) hnpos
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
    exact hybrid_domain_subset_parent i
  have hBook : Book.Ch02.coarseBlockMatrix T aT = A := by
    simpa only [A, S, V, P, n] using
      attenuated_domain_matrix_eq M P n (Q.scale-342) J hn hmJ weights ω
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
      hUL.conjTranspose_mul_mul_same (C i)
  have hLR' : A'.lowerRight.PosSemidef := by
    simpa [A', D] using
      hLR.conjTranspose_mul_mul_same D
  have hsum (s : ℝ) (hs : 0 < s) :
      (∑ j : Fin 2 × Bool, hybridFullTraceCellLoadEnergy s A (C i) j) =
        Matrix.trace (toFullBlockMat (frameMatrix s A')) := by
    rw [hybrid_full_trace_cell_load_sum_eq s A (C i) hs]
    simp [A', D, frameMatrix,
      toFullBlockMat, Matrix.trace, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.diag_apply]
    ring
  have hframeTrace := full_response_framed_trace_le_of_scalar_frame_growth
    A' σold σ G hσold hholdle hG hratio hUL'.trace_nonneg hLR'.trace_nonneg
  have hrootReal :
      (∑ j : Fin 2 × Bool, hybridFullTraceCellLoadEnergy σ A (C i) j) ≤
        G * (∑ j : Fin 2 × Bool,
          hybridFullTraceCellLoadEnergy σold A (C i) j) := by
    rw [hsum σ hσ, hsum σold hσold]
    exact hframeTrace
  have hG0 : 0 ≤ G := le_trans (by norm_num : (0:ℝ) ≤ 1) hG
  calc
    _ ≤ ENNReal.ofReal (G *
        (∑ j : Fin 2 × Bool,
          hybridFullTraceCellLoadEnergy σold A (C i) j)) :=
      ENNReal.ofReal_le_ofReal hrootReal
    _ = ENNReal.ofReal G * ENNReal.ofReal
        (∑ j : Fin 2 × Bool,
          hybridFullTraceCellLoadEnergy σold A (C i) j) :=
      ENNReal.ofReal_mul hG0

/-- The transformed four-load sum on an actual active hybrid simplex, viewed
in the observer frame, is at most the exact parent-frame load sum times the
root-gap and selected-layer clock. -/
theorem full_response_active_load_sum_reference_frame_le
    (M : ABKModel 2) (Q : TriadicCube 2) (H : ℕ)
    (hH : 377 ≤ H) (ω : Cutoff.CutoffSample 2)
    (J : ℤ) (hmJ : Q.scale-342 ≤ J)
    (weights : ℤ → ℝ)
    (C : HybridCell Q H (rootBadWhitneyCells M Q H (rootTau .full)
      (ASDExplicitGamma.Gaussian.waveGateEta .full) ω) → Mat 2)
    (i : HybridActiveCell Q H (rootBadWhitneyCells M Q H (rootTau .full)
      (ASDExplicitGamma.Gaussian.waveGateEta .full) ω)) :
    let U := (hybridParent (.inr i)).2.val
    let n := U.scale + 40
    let σ := (Annealed.sigmaBar M (Q.scale-1) : ℝ)
    let σold := (Annealed.sigmaBar M n : ℝ)
    let G := rootAssemblyClock M.gamma H (hybridParent (.inr i)).1
    ENNReal.ofReal (∑ j : Fin 2 × Bool,
      hybridFullTraceCellLoadEnergy σ
        (coarseBlockMatrix (hybridDomain (.inr i) : Set (Vec 2))
          (attenuatedCoefficient M (Q.scale-342) J weights ω)) (C (.inr i)) j) ≤
      ENNReal.ofReal G * ENNReal.ofReal (∑ j : Fin 2 × Bool,
        hybridFullTraceCellLoadEnergy σold
          (coarseBlockMatrix (hybridDomain (.inr i) : Set (Vec 2))
            (attenuatedCoefficient M (Q.scale-342) J weights ω)) (C (.inr i)) j) := by
  exact full_response_cell_load_sum_reference_frame_le M Q H hH ω J hmJ weights C (.inr i)

/-- The exact c₀ₜ/c₁ₜ active cap in the root reference frame, starting from
the protected completed law. It includes the endpoint terminal label l-1. -/
theorem full_response_active_reference_trace_root_mean_le
    (M : ABKModel 2) (Q : TriadicCube 2) (H : ℕ) (hH : 377 ≤ H)
    (ω : Cutoff.CutoffSample 2) (J : ℤ) (hJ : Q.scale-1 ≤ J)
    (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc (Q.scale-342) J, 0 ≤ weights k ∧ weights k ≤ 1)
    (C : HybridCell Q H (rootBadWhitneyCells M Q H (rootTau .full)
      (ASDExplicitGamma.Gaussian.waveGateEta .full) ω) → Mat 2)
    (i : HybridActiveCell Q H (rootBadWhitneyCells M Q H (rootTau .full)
      (ASDExplicitGamma.Gaussian.waveGateEta .full) ω))
    (hnotbad : (hybridParent (.inr i)).2.val ∉
      rootBadWhitneyCells M Q H (rootTau .full)
        (ASDExplicitGamma.Gaussian.waveGateEta .full) ω) :
    let m := Q.scale-342
    let P := (hybridParent (.inr i)).2.val
    ENNReal.ofReal (∑ j : Fin 2 × Bool,
      hybridFullTraceCellLoadEnergy (Annealed.sigmaBar M (Q.scale-1) : ℝ)
        (coarseBlockMatrix (hybridDomain (.inr i) : Set (Vec 2))
          (attenuatedCoefficient M m J weights ω)) (C (.inr i)) j) ≤
      ENNReal.ofReal (rootAssemblyClock M.gamma H (hybridParent (.inr i)).1) *
        (ENNReal.ofReal (4 * ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (C (.inr i))‖^2) *
          ENNReal.ofReal (rootEdelta .full * (fullResponseTraceC0 +
            fullResponseTraceC1 * (fullResponseParentWaveMean M P m J weights ω)^2))) := by
  classical
  dsimp only
  let P := (hybridParent (.inr i)).2.val
  let U := i.2.val.supportCube
  let pi := i.2.val.order
  have hH0 : heightEntrance 0 ≤ H := by
    simpa only [heightEntrance, mul_zero, add_zero] using hH
  have hnpos := root_whitney_layer_pos Q H i.1.val.1 i.1.val.2.property
  have hn : P.scale+40 ≤ Q.scale-342 := by
    have hh := layer_old_cutoff_le_protected Q.scale 0 H i.1.val.1 hH0 hnpos
    rw [root_whitney_old_cutoff_eq Q H i.1.val.1 i.1.val.2.property] at hh
    simpa only [P, hybridParent, protectedOldLabel, Nat.cast_zero, mul_zero, sub_zero] using hh
  have hgood := hybrid_parent_good_of_not_bad M Q H (rootTau .full)
    (ASDExplicitGamma.Gaussian.waveGateEta .full) ω (.inr i) hnotbad
  obtain ⟨a, ha, hdepth⟩ := final_kuhn_support_depth_le_two Q H
    i.1.val.1 i.1.val.2.property i.2.property
  have hlocal := good_parent_active_triangle_transformed_full_trace_sharp_root_mean
    M hdepth ha pi (Q.scale-342) J hn (by omega) weights hw ω hgood (C (.inr i))
  have hK : i.2.val = Whitney.KuhnCell.mk U pi := by dsimp only [U, pi]
  rw [← hK] at hlocal
  have hframe := full_response_active_load_sum_reference_frame_le
    M Q H hH ω J (by omega) weights C i
  apply hframe.trans
  apply mul_le_mul_of_nonneg_left _ bot_le
  convert! hlocal using 1

end
end ASDExplicitGamma.Inverse
