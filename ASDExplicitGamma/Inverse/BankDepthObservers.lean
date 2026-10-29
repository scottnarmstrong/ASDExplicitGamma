module

public import ASDExplicitGamma.Inverse.BankDepthBlocks
public import ASDExplicitGamma.Inverse.BankObservers

/-! Source observer populations for the unbounded depth extension. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization Algsuperdiff.Section3

noncomputable def bankObserverDepthRoots (Q : TriadicCube 2) (r0 j : ℕ) :
    Finset (TriadicCube 2) := descendantsAtDepth Q (40+r0+j)

noncomputable def bankObserverDepthRootUnion (Q : TriadicCube 2) (rmax j : ℕ) :
    Finset (TriadicCube 2) := by
  classical
  exact (Finset.range (rmax+1)).biUnion (fun r0 => bankObserverDepthRoots Q r0 j)

theorem bank_observer_depth_roots_card (Q : TriadicCube 2) (r0 j : ℕ) :
    (bankObserverDepthRoots Q r0 j).card = 9^(40+r0+j) := by
  unfold bankObserverDepthRoots
  rw [descendantsAtDepth_card]
  norm_num

theorem bank_observer_depth_roots_scale (Q : TriadicCube 2) (m : ℤ)
    (hQ : Q.scale = m+40) (r0 j : ℕ) {U : TriadicCube 2}
    (hU : U ∈ bankObserverDepthRoots Q r0 j) : U.scale = m-(r0:ℤ)-(j:ℤ) := by
  have hs := scale_eq_sub_of_mem_descendantsAtDepth hU
  rw [hQ] at hs
  omega

/-- Every depth-j descendant of a source root belongs to the paid depth population. -/
theorem bank_observer_depth_roots_mem (Q : TriadicCube 2) (r0 j : ℕ)
    {U V : TriadicCube 2} (hU : U ∈ bankObserverRoots Q r0)
    (hV : V ∈ descendantsAtDepth U j) : V ∈ bankObserverDepthRoots Q r0 j :=
  mem_descendantsAtDepth_add hU hV

theorem bank_observer_depth_roots_geometry (Q : TriadicCube 2) (m : ℤ)
    (hQ : Q.scale = m+40) (r0 : ℕ) (hr : r0 ≤ 5) (j : ℕ) :
    (∀ U ∈ bankObserverDepthRoots Q r0 j,
      U.scale ≤ m-(j:ℤ) ∧ (m-(j:ℤ))-U.scale ≤ 5) ∧
      (bankObserverDepthRoots Q r0 j).card ≤ 6*9^(45+j) := by
  refine ⟨?_,?_⟩
  · intro U hU
    have hs := bank_observer_depth_roots_scale Q m hQ r0 j hU
    omega
  · rw [bank_observer_depth_roots_card]
    exact (pow_le_pow_right₀ (by norm_num : (1:ℕ) ≤ 9)
      (by omega : 40+r0+j ≤ 45+j)).trans (by omega)

theorem bank_observer_depth_union_geometry (Q : TriadicCube 2) (m : ℤ)
    (hQ : Q.scale = m+40) (rmax : ℕ) (hr : rmax ≤ 5) (j : ℕ) :
    (∀ U ∈ bankObserverDepthRootUnion Q rmax j,
      U.scale ≤ m-(j:ℤ) ∧ (m-(j:ℤ))-U.scale ≤ 5) ∧
      (bankObserverDepthRootUnion Q rmax j).card ≤ 6*9^(45+j) := by
  classical
  refine ⟨?_,?_⟩
  · intro U hU
    obtain ⟨r0,hr0,hU⟩ := Finset.mem_biUnion.mp hU
    have hr0' : r0 ≤ 5 := by have := Finset.mem_range.mp hr0; omega
    exact (bank_observer_depth_roots_geometry Q m hQ r0 hr0' j).1 U hU
  · unfold bankObserverDepthRootUnion
    calc
      _ ≤ ∑ r0 ∈ Finset.range (rmax+1), (bankObserverDepthRoots Q r0 j).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _r0 ∈ Finset.range (rmax+1), 9^(45+j) := by
        apply Finset.sum_le_sum
        intro r0 hr0
        rw [bank_observer_depth_roots_card]
        have hr0' := Finset.mem_range.mp hr0
        exact pow_le_pow_right₀ (by norm_num : (1:ℕ) ≤ 9)
          (by omega : 40+r0+j ≤ 45+j)
      _ = (rmax+1)*9^(45+j) := by simp
      _ ≤ 6*9^(45+j) := Nat.mul_le_mul_right _ (by omega : rmax+1 ≤ 6)

/-- OLD local families may include all six source refinement offsets. -/
theorem inverse_bank_observer_union_depths
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (r : InverseBankRow) (Q : TriadicCube 2) (m J : ℤ) (hQ : Q.scale = m+40)
    (hmJ : m ≤ J) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (rmax : ℕ) (hr : rmax ≤ 5) (hpast : ∀ n < m, nativeInductionState M h n)
    (hmean : ClippedInverseMeanInput M m (inverseBankRootRow r)) :
    ∀ j : ℕ,
      InverseBankDepthConclusion M r (bankObserverDepthRootUnion Q rmax j) m J weights j ∧
      InverseBankDepthBlockConclusion M r (bankObserverDepthRootUnion Q rmax j) m J weights j := by
  intro j
  have hgeometry := bank_observer_depth_union_geometry Q m hQ rmax hr j
  exact ⟨inverse_bank_depth_history M h hM hg r _ m J hmJ weights hw j
      hgeometry.1 hgeometry.2 hpast hmean,
    inverse_bank_depth_block M h hM hg r _ m J hmJ weights hw j
      hgeometry.1 hgeometry.2 hpast hmean⟩

end ASDExplicitGamma.Inverse
