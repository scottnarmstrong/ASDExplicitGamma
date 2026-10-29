module

public import ASDExplicitGamma.Inverse.BankGlobal
public import ASDExplicitGamma.Inverse.BankHistoryPhysical
public import ASDExplicitGamma.Inverse.BankOnePassLocal
public import ASDExplicitGamma.Inverse.BridgeObservables

/-! Actual global inverse-bank input for the mixed-bridge observer history. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open ASDExplicitGamma.Scalar ASDExplicitGamma.Variational
open scoped ENNReal

theorem ennreal_finset_sup_ofReal {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) :
    ENNReal.ofReal (Book.Ch02.finsetSupReal s f) =
      s.sup (fun i => ENNReal.ofReal (f i)) := by
  have hh := (bank_finite_max_ofReal s hs f).symm
  have huniv : (Finset.univ : Finset ↥s) = s.attach := by
    ext i
    simp
  calc
    _ = (Finset.univ : Finset ↥s).sup (fun i => ENNReal.ofReal (f i.1)) := by
      simpa only [historyFiniteMax] using hh
    _ = s.attach.sup (fun i => ENNReal.ofReal (f i.1)) := by rw [huniv]
    _ = s.sup (fun i => ENNReal.ofReal (f i)) :=
      Finset.sup_attach s (fun i => ENNReal.ofReal (f i))

/-- The exact six-root observer family is the five-offset bank union. -/
theorem mixed_bridge_observer_roots_eq_bank_union (m : ℤ) :
    mixedBridgeObserverSourceRoots m =
      bankObserverRootUnion (originCube 2 (m + 40)) 5 := by
  rfl

theorem grouped_bank_history_eq_union_sup
    (Q : TriadicCube 2) (M : ABKModel 2) (m J : ℤ)
    (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) (f : TriadicCube 2 → ℝ≥0∞)
    (hroot : ∀ r (U : TriadicCube 2), U ∈ bankObserverRoots Q r →
      bankRootInverseHistory U M m J weights ω = f U) :
    inverseBankGroupedHistory (Finset.range 6) (bankObserverRoots Q) M m J weights ω =
      (bankObserverRootUnion Q 5).sup f := by
  have hfamily (r : ℕ) :
      bankFiniteRootHistoryMax (bankObserverRoots Q r) M m J weights ω =
        (bankObserverRoots Q r).sup (fun U => f U) := by
    unfold bankFiniteRootHistoryMax historyFiniteMax
    change (bankObserverRoots Q r).attach.sup
      (fun U => bankRootInverseHistory U.1 M m J weights ω) = _
    calc
      _ = (bankObserverRoots Q r).sup
          (fun U => bankRootInverseHistory U M m J weights ω) :=
        Finset.sup_attach (bankObserverRoots Q r)
          (fun U => bankRootInverseHistory U M m J weights ω)
      _ = _ := by
        apply Finset.sup_congr rfl
        intro U hU
        exact hroot r U hU
  unfold inverseBankGroupedHistory historyFiniteMax bankObserverRootUnion
  rw [Finset.sup_biUnion]
  apply Finset.sup_congr rfl
  intro r hr
  exact hfamily r

theorem bank_union_history_max_eq_grouped
    (Q : TriadicCube 2) (M : ABKModel 2) (m J : ℤ)
    (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) :
    bankFiniteRootHistoryMax (bankObserverRootUnion Q 5) M m J weights ω =
      inverseBankGroupedHistory (Finset.range 6) (bankObserverRoots Q) M m J weights ω := by
  have hfamily (r : ℕ) :
      bankFiniteRootHistoryMax (bankObserverRoots Q r) M m J weights ω =
        (bankObserverRoots Q r).sup
          (fun U => bankRootInverseHistory U M m J weights ω) := by
    unfold bankFiniteRootHistoryMax historyFiniteMax
    change (bankObserverRoots Q r).attach.sup
      (fun U => bankRootInverseHistory U.1 M m J weights ω) = _
    exact Finset.sup_attach (bankObserverRoots Q r)
      (fun U => bankRootInverseHistory U M m J weights ω)
  calc
    _ = (bankObserverRootUnion Q 5).sup
        (fun U => bankRootInverseHistory U M m J weights ω) := by
      unfold bankFiniteRootHistoryMax historyFiniteMax
      change (bankObserverRootUnion Q 5).attach.sup
        (fun U => bankRootInverseHistory U.1 M m J weights ω) = _
      exact Finset.sup_attach (bankObserverRootUnion Q 5)
        (fun U => bankRootInverseHistory U M m J weights ω)
    _ = (Finset.range 6).sup (fun r => (bankObserverRoots Q r).sup
        (fun U => bankRootInverseHistory U M m J weights ω)) := by
      unfold bankObserverRootUnion
      rw [Finset.sup_biUnion]
    _ = inverseBankGroupedHistory (Finset.range 6) (bankObserverRoots Q)
        M m J weights ω := by
      unfold inverseBankGroupedHistory historyFiniteMax
      apply Finset.sup_congr rfl
      intro r hr
      exact (hfamily r).symm

private theorem mixed_bridge_bank_coefficient_eq
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    attenuatedCoefficient M m (m + 40)
        (bankPartialInsertionWeights m 1 t) ω =
      (Model.partialInsertedCoefficient M m t ω).toFun := by
  calc
    _ = (Model.partialInsertedCoefficient M (m + (1 : ℤ) - 1) t ω).toFun :=
      bank_one_pass_partial_coefficient M m 1 (by norm_num) t ω
    _ = (Model.partialInsertedCoefficient M m t ω).toFun := by
      rw [show m + (1 : ℤ) - 1 = m by omega]

theorem mixed_bridge_bank_root_history_physical
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (ω : Cutoff.CutoffSample 2) (r : ℕ) (U : TriadicCube 2)
    (hU : U ∈ bankObserverRoots (originCube 2 (m + 40)) r) :
    bankRootInverseHistory U M m (m + 40) (bankPartialInsertionWeights m 1 t) ω =
      ENNReal.ofReal (mixedBridgeRootHistoryProfile M m t ω U) := by
  have hUdesc : U ∈ descendantsAtDepth (originCube 2 (m + 40)) (40 + r) := by
    exact hU
  have hEll := Model.partialInsertedCoefficient_isEllipticFieldOn M (m + 40) m ω
    ⟨ht.1, ht.2⟩ (measurableSet_openCubeSet U)
    (openCubeSet_subset_of_mem_descendantsAtDepth hUdesc)
  have hcoeff := mixed_bridge_bank_coefficient_eq M m t ω
  simpa only [mixedBridgeRootHistoryProfile] using
    bank_root_history_physical U M m (m + 40)
    (bankPartialInsertionWeights m 1 t) ω
    (Model.partialInsertedCoefficient M m t ω).toFun hcoeff hEll

/-- The exported real `B*` is exactly the ENNReal bank maximum. -/
theorem mixed_bridge_bstar_eq_global_bank_history
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (ω : Cutoff.CutoffSample 2) :
    ENNReal.ofReal (mixedBridgeBstar M m t ω) =
      inverseBankGroupedHistory (Finset.range 6)
        (bankObserverRoots (originCube 2 (m + 40)))
        M m (m + 40) (bankPartialInsertionWeights m 1 t) ω := by
  classical
  have hs : (bankObserverRootUnion (originCube 2 (m + 40)) 5).Nonempty := by
    change ((Finset.range 6).biUnion
      (bankObserverRoots (originCube 2 (m + 40)))).Nonempty
    apply Finset.Nonempty.biUnion
    · exact ⟨0, by simp⟩
    · intro r _
      exact descendantsAtDepth_nonempty _ _
  have hroots : mixedBridgeObserverSourceRoots m =
      bankObserverRootUnion (originCube 2 (m + 40)) 5 := by
    exact mixed_bridge_observer_roots_eq_bank_union m
  change ENNReal.ofReal (Book.Ch02.finsetSupReal (mixedBridgeObserverSourceRoots m)
      (mixedBridgeRootHistoryProfile M m t ω)) = _
  rw [hroots]
  let f : TriadicCube 2 → ℝ := mixedBridgeRootHistoryProfile M m t ω
  have hroot : ∀ r (U : TriadicCube 2),
      U ∈ bankObserverRoots (originCube 2 (m + 40)) r →
      bankRootInverseHistory U M m (m + 40) (bankPartialInsertionWeights m 1 t) ω =
        ENNReal.ofReal (f U) := by
    intro r U hU
    change bankRootInverseHistory U M m (m + 40) (bankPartialInsertionWeights m 1 t) ω =
      ENNReal.ofReal (mixedBridgeRootHistoryProfile M m t ω U)
    exact mixed_bridge_bank_root_history_physical M m t ht ω r U hU
  have hraw := ennreal_finset_sup_ofReal
    (bankObserverRootUnion (originCube 2 (m + 40)) 5) hs f
  have hgroup := grouped_bank_history_eq_union_sup
    (originCube 2 (m + 40)) M m (m + 40) (bankPartialInsertionWeights m 1 t) ω
    (fun U => ENNReal.ofReal (f U)) hroot
  exact hraw.trans hgroup.symm

theorem mixed_bridge_bstar_eq_bank_finite_history
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (ω : Cutoff.CutoffSample 2) :
    ENNReal.ofReal (mixedBridgeBstar M m t ω) =
      bankFiniteRootHistoryMax (mixedBridgeObserverSourceRoots m)
        M m (m + 40) (bankPartialInsertionWeights m 1 t) ω := by
  change ENNReal.ofReal (mixedBridgeBstar M m t ω) =
    bankFiniteRootHistoryMax (bankObserverRootUnion (originCube 2 (m + 40)) 5)
      M m (m + 40) (bankPartialInsertionWeights m 1 t) ω
  calc
    _ = inverseBankGroupedHistory (Finset.range 6)
          (bankObserverRoots (originCube 2 (m + 40)))
          M m (m + 40) (bankPartialInsertionWeights m 1 t) ω :=
      mixed_bridge_bstar_eq_global_bank_history M m t ht ω
    _ = bankFiniteRootHistoryMax (bankObserverRootUnion (originCube 2 (m + 40)) 5)
          M m (m + 40) (bankPartialInsertionWeights m 1 t) ω :=
      (bank_union_history_max_eq_grouped (originCube 2 (m + 40)) M m (m + 40)
        (bankPartialInsertionWeights m 1 t) ω).symm

/-- The actual global observer bank, instantiated on the exact mixed-bridge
root union from the pre-insertion strict-past native states. -/
theorem mixed_bridge_global_bank_inputs
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (m : ℤ) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hstate : ∀ j : ℕ, nativeInductionState M h (m - (j : ℤ))) :
    InverseBankConclusion M .globalInverse (mixedBridgeObserverSourceRoots m)
      m (m + 40) (bankPartialInsertionWeights m 1 t) := by
  let Q := originCube 2 (m + 40)
  have hQ : Q.scale = m + 40 := rfl
  have hpast : ∀ n < m, nativeInductionState M h n := by
    intro n hn
    have hdiff : 0 ≤ m - n := by omega
    have hcast : (Int.toNat (m - n) : ℤ) = m - n := Int.toNat_of_nonneg hdiff
    have hindex : m - (Int.toNat (m - n) : ℤ) = n := by rw [hcast]; omega
    rw [← hindex]
    exact hstate (Int.toNat (m - n))
  have hgeo := bank_observer_union_geometry Q m hQ 5 le_rfl
  have hw : ∀ k ∈ Finset.Ioc m (m + 40),
      0 ≤ bankPartialInsertionWeights m 1 t k ∧
        bankPartialInsertionWeights m 1 t k ≤ 1 :=
    fun k _ => bank_partial_insertion_weights_bounds m 1 t ht.2 k
  have hmean := (bank_inverse_mean_inputs_of_states M h hM hγ m hpast).1
  have hbank := global_inverse_bank M h hM hγ (bankObserverRootUnion Q 5)
    m (m + 40) (by omega) (bankPartialInsertionWeights m 1 t) hw
    hgeo.1 hgeo.2 hpast hmean
  rw [← mixed_bridge_observer_roots_eq_bank_union m] at hbank
  exact hbank

/-- The `B*` cap and global rare split consumed by the correlated bridge rows. -/
theorem mixed_bridge_global_bank_split
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (m : ℤ) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hstate : ∀ j : ℕ, nativeInductionState M h (m - (j : ℤ))) :
    (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ENNReal.ofReal (mixedBridgeBstar M m t ω) ≤
        ENNReal.ofReal (inverseBankCap .globalInverse) +
          ENNReal.ofReal (inverseBankPopulationRemainder .globalInverse
            (mixedBridgeObserverSourceRoots m) M m (m + 40)
            (bankPartialInsertionWeights m 1 t) ω)) ∧
    eLpNorm (fun ω => ENNReal.ofReal (mixedBridgeBstar M m t ω)) 128
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (inverseBankCap .globalInverse) ∧
    eLpNorm (inverseBankPopulationRemainder .globalInverse
      (mixedBridgeObserverSourceRoots m) M m (m + 40)
      (bankPartialInsertionWeights m 1 t)) 128
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (inverseBankReserve .globalInverse) := by
  have hbank := mixed_bridge_global_bank_inputs M h hM hγ m t ht hstate
  refine ⟨?_, ?_, hbank.remainder_L128⟩
  · filter_upwards [hbank.history_le] with ω hω
    rw [mixed_bridge_bstar_eq_bank_finite_history M m t ht ω]
    exact hω
  · have hEq : (fun ω => ENNReal.ofReal (mixedBridgeBstar M m t ω)) =
      bankFiniteRootHistoryMax (mixedBridgeObserverSourceRoots m)
        M m (m + 40) (bankPartialInsertionWeights m 1 t) := by
      funext ω
      exact mixed_bridge_bstar_eq_bank_finite_history M m t ht ω
    rw [hEq]
    exact hbank.total_L128

end ASDExplicitGamma.Inverse
