module

public import ASDExplicitGamma.Inverse.HybridGradientConstants
public import ASDExplicitGamma.Inverse.ActiveTriangleResponse
public import ASDExplicitGamma.Inverse.GoodCellClippedResponse
public import ASDExplicitGamma.Inverse.FluxNorm

/-! Actual local response bounds on both parts of the literal hybrid family. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider Algsuperdiff.Section3.Provider.Whitney
noncomputable section

/-- Every final source simplex support has genuine parent depth at most two. -/
theorem final_kuhn_support_depth_le_two (Q : TriadicCube 2) (H n : ℕ)
    {P : TriadicCube 2} (hP : P ∈ whitneyRootLayer Q H n)
    {T : KuhnCell 2} (hT : T ∈ finalWhitneyKuhnCells Q H n P) :
    ∃ a : ℕ, a ≤ 2 ∧ T.supportCube ∈ descendantsAtDepth P a := by
  have hd := final_whitney_kuhn_depth_range Q H n hP
  change T ∈ triadicSimplexPartition P (Q.scale-(compatibleWhitneyMeshDepth H (n+1):ℤ)) at hT
  rw [mem_triadicSimplexPartition_iff,descendantsAtScale_eq_descendantsAtDepth P hd.1] at hT
  exact ⟨_,by omega,hT⟩

/-- Each hybrid parent uses a strictly earlier completed old label. -/
theorem hybrid_parent_old_label_lt (Q : TriadicCube 2) (H : ℕ) (hH : 333 ≤ H)
    (S : Set (TriadicCube 2)) (m : ℤ) (hQ : Q.scale ≤ m) (i : HybridCell Q H S) :
    (hybridParent i).2.val.scale+40 < m := by
  have hs := root_whitney_layer_scale Q H (hybridParent i).1 (hybridParent i).2.property
  have hn := root_whitney_layer_pos Q H (hybridParent i).1 (hybridParent i).2.property
  unfold whitneyProfile at hs
  omega

/-- Whole identity cells are genuinely good for the actual bad-cell family. -/
theorem hybrid_identity_parent_good (M : ABKModel 2) (Q : TriadicCube 2) (H : ℕ)
    (τ η : ℝ) (ω : Cutoff.CutoffSample 2)
    (i : HybridIdentityCell Q H (rootBadWhitneyCells M Q H τ η ω)) :
    ω ∉ cellFailure M τ η i.val.2.val := by
  intro hfail
  have hparent := (root_partition_iff_layer Q H _).mpr ⟨i.val.1,i.val.2.property⟩
  exact i.property i.val.2.val ⟨hparent,hfail⟩ (cubeTouch_refl _)

/-- Any nonbad actual hybrid parent is good at exactly its own gate label. -/
theorem hybrid_parent_good_of_not_bad (M : ABKModel 2) (Q : TriadicCube 2) (H : ℕ)
    (τ η : ℝ) (ω : Cutoff.CutoffSample 2)
    (i : HybridCell Q H (rootBadWhitneyCells M Q H τ η ω))
    (hi : (hybridParent i).2.val ∉ rootBadWhitneyCells M Q H τ η ω) :
    ω ∉ cellFailure M τ η (hybridParent i).2.val := by
  intro hfail
  exact hi ⟨(root_partition_iff_layer Q H _).mpr
    ⟨(hybridParent i).1,(hybridParent i).2.property⟩,hfail⟩

/-- The whole identity-cell response is bounded by its actual clipped
matrix, in exactly its own old true frame. -/
theorem hybrid_identity_response_bound (M : ABKModel 2) (Q : TriadicCube 2)
    (H : ℕ) (hH : 333 ≤ H) (r : RootRow) (ω : Cutoff.CutoffSample 2)
    (m J : ℤ) (hQ : Q.scale ≤ m) (hm : m ≤ J) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (i : HybridIdentityCell Q H (rootBadWhitneyCells M Q H (rootTau r)
      (ASDExplicitGamma.Gaussian.waveGateEta (rootWaveTuple r)) ω)) (q : Vec 2) :
    (Annealed.sigmaBar M (i.val.2.val.scale+40):ℝ)*dotProduct q
      ((coarseBlockMatrix (hybridDomain (.inl i):Set (Vec 2))
        (attenuatedCoefficient M m J weights ω)).lowerRight.mulVec q) ≤
      rootEdelta r*fullMatrixQuadratic (toFullBlockVec (0,q))
        (clippedCellMatrix M (i.val.2.val.scale+40) i.val.2.val (rootTau r) ω) := by
  have hn := (hybrid_parent_old_label_lt Q H hH _ m hQ (.inl i)).le
  have hh := good_cell_clipped_pure_flux_response M i.val.2.val r m J hn hm weights hw ω
    (hybrid_identity_parent_good M Q H _ _ ω i) q
  rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube] at hh
  exact hh

/-- Every active simplex obeys the same source cap. On bad parents its
common slope vanishes, and the actual trial energy is exactly zero. -/
theorem hybrid_active_response_bound (M : ABKModel 2) (Q : TriadicCube 2)
    (H : ℕ) (hH : 333 ≤ H) (r : RootRow) (ω : Cutoff.CutoffSample 2)
    (m J : ℤ) (hQ : Q.scale ≤ m) (hm : m ≤ J) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (C : HybridCell Q H (rootBadWhitneyCells M Q H (rootTau r)
      (ASDExplicitGamma.Gaussian.waveGateEta (rootWaveTuple r)) ω) → Mat 2)
    (hCb : ∀ i, (hybridParent i).2.val ∈ rootBadWhitneyCells M Q H (rootTau r)
      (ASDExplicitGamma.Gaussian.waveGateEta (rootWaveTuple r)) ω → C i=0)
    (i : HybridActiveCell Q H (rootBadWhitneyCells M Q H (rootTau r)
      (ASDExplicitGamma.Gaussian.waveGateEta (rootWaveTuple r)) ω)) (q : Vec 2) :
    let v := matVecMul (planarFluxMatrix (C (.inr i))) q
    (Annealed.sigmaBar M (i.1.val.2.val.scale+40):ℝ)*dotProduct v
      ((coarseBlockMatrix (hybridDomain (.inr i):Set (Vec 2))
        (attenuatedCoefficient M m J weights ω)).lowerRight.mulVec v) ≤
      rootEdelta r*rootResponseEnvelope (6*rootTau r)*dotProduct v v := by
  classical
  by_cases hb : i.1.val.2.val ∈ rootBadWhitneyCells M Q H (rootTau r)
      (ASDExplicitGamma.Gaussian.waveGateEta (rootWaveTuple r)) ω
  · dsimp only
    rw [hCb (.inr i) hb,planar_flux_matrix_zero]
    simp [matVecMul]
  · have hg := hybrid_parent_good_of_not_bad M Q H _ _ ω (.inr i) hb
    obtain ⟨a,ha,hTa⟩ := final_kuhn_support_depth_le_two Q H i.1.val.1 i.1.val.2.property i.2.property
    exact good_parent_active_triangle_response M hTa ha i.2.val.order r m J
      (hybrid_parent_old_label_lt Q H hH _ m hQ (.inr i)).le hm weights hw ω hg _

end
end ASDExplicitGamma.Inverse
