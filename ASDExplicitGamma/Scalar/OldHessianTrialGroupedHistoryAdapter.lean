module

public import ASDExplicitGamma.Scalar.OldHessianTrialPhysicalHistory
public import ASDExplicitGamma.Scalar.OldHessianTrialGroupedBank
public import ASDExplicitGamma.Scalar.OldHessianTrialPrincipalBudget
public import ASDExplicitGamma.Inverse.BridgeGlobalBank

/-! The actual fine histories inside Q_(m+129) are dominated by the exact
9^89 grouped bank. Only the original rare reserve is population charged. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Algsuperdiff.Section3
open scoped ENNReal
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- Every actual source cell lies in one of the original six-level observer
families of a genuine scale-(m+40) macrocell. -/
theorem old_hessian_source_cell_observer (m : ℤ) (r : ℕ) (hr : r≤5)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 (m+129)) (129+r)) :
    ∃ D ∈ oldHessianMacroCells m,U ∈ bankObserverRootUnion D 5 := by
  classical
  have hdepth : 129+r=89+(40+r) := by omega
  rw [hdepth] at hU
  obtain ⟨D,hD,hUD⟩ := exists_descendant_ancestor_at_depth 89 (40+r) hU
  refine ⟨D,hD,?_⟩
  change U ∈ (Finset.range 6).biUnion (bankObserverRoots D)
  exact Finset.mem_biUnion.mpr ⟨r,Finset.mem_range.mpr (by omega),hUD⟩

/-- Exact extended domination: an infinite grouped history cannot disappear
through toReal in the physical source-bank identification. -/
theorem old_hessian_fine_history_ofReal_le_grouped (M : ABKModel 2) (m : ℤ)
    (omega : Cutoff.CutoffSample 2) (r : ℕ) (hr : r≤5) :
    ENNReal.ofReal (oldHessianFineInverseHistory (originCube 2 (m+129)) (129+r)
      M.nu (Annealed.sigmaBar M m) (oldHessianOldOpenCoefficient (m+129) m omega)) ≤
      inverseBankGroupedHistory (oldHessianMacroCells m) (fun D => bankObserverRootUnion D 5)
        M m (m+40) (bankPartialInsertionWeights m 1 0) omega := by
  classical
  unfold oldHessianFineInverseHistory
  rw [ennreal_finset_sup_ofReal _ (descendantsAtDepth_nonempty _ _) _]
  apply Finset.sup_le
  intro U hU
  rw [←old_hessian_physical_root_history M (m+129) m omega U
    (openCubeSet_subset_of_mem_descendantsAtDepth hU)]
  obtain ⟨D,hD,hUD⟩ := old_hessian_source_cell_observer m r hr U hU
  have hroot : bankRootInverseHistory U M m (m+40) (bankPartialInsertionWeights m 1 0) omega ≤
      bankFiniteRootHistoryMax (bankObserverRootUnion D 5) M m (m+40) (bankPartialInsertionWeights m 1 0) omega := by
    unfold bankFiniteRootHistoryMax historyFiniteMax
    exact Finset.le_sup (f := fun V : ↥(bankObserverRootUnion D 5) =>
      bankRootInverseHistory V.val M m (m+40) (bankPartialInsertionWeights m 1 0) omega)
      (Finset.mem_univ (⟨U,hUD⟩ : ↥(bankObserverRootUnion D 5)))
  exact hroot.trans (Finset.le_sup (f := fun D =>
    bankFiniteRootHistoryMax (bankObserverRootUnion D 5) M m (m+40) (bankPartialInsertionWeights m 1 0) omega) hD)

/-- The actual r0..r5 physical inverse histories share one finite real
scalar bank on a common event, with all bank inputs proved from past states. -/
theorem old_hessian_actual_fine_histories_le_bank
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma≤gammaZero)
    (N : ℤ) (hpast : ∀ k<N,nativeInductionState M h k) (m : ℤ) (hm : m<N) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure, ∀ r : ℕ,r≤5 →
      oldHessianFineInverseHistory (originCube 2 (m+129)) (129+r)
        M.nu (Annealed.sigmaBar M m) (oldHessianOldOpenCoefficient (m+129) m omega) ≤
      (inverseBankGroupedHistory (oldHessianMacroCells m) (fun D => bankObserverRootUnion D 5)
        M m (m+40) (bankPartialInsertionWeights m 1 0) omega).toReal := by
  filter_upwards [old_hessian_parent_grouped_split M h hM hg N hpast m hm] with omega homega
  intro r hr
  have hh := ENNReal.toReal_mono homega.1.ne (old_hessian_fine_history_ofReal_le_grouped M m omega r hr)
  rw [ENNReal.toReal_ofReal (old_hessian_fine_history_nonneg _ _ _ _ _)] at hh
  exact hh

end
end ASDExplicitGamma.Scalar
