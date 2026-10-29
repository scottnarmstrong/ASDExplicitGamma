module

public import ASDExplicitGamma.Inverse.BankInverse

/-! Source observer root families and deterministic partial-insertion weights. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization Algsuperdiff.Section3

noncomputable def bankObserverRoots (Q : TriadicCube 2) (r0 : ℕ) : Finset (TriadicCube 2) :=
  descendantsAtDepth Q (40+r0)

noncomputable def bankObserverRootUnion (Q : TriadicCube 2) (rmax : ℕ) :
    Finset (TriadicCube 2) := by
  classical
  exact (Finset.range (rmax+1)).biUnion (bankObserverRoots Q)

theorem bank_observer_roots_card (Q : TriadicCube 2) (r0 : ℕ) :
    (bankObserverRoots Q r0).card = 9^(40+r0) := by
  unfold bankObserverRoots
  rw [descendantsAtDepth_card]
  norm_num

theorem bank_observer_roots_scale (Q : TriadicCube 2) (m : ℤ)
    (hQ : Q.scale = m+40) (r0 : ℕ) {U : TriadicCube 2}
    (hU : U ∈ bankObserverRoots Q r0) : U.scale = m-(r0:ℤ) := by
  have hs := scale_eq_sub_of_mem_descendantsAtDepth hU
  rw [hQ] at hs
  omega

theorem bank_observer_roots_geometry (Q : TriadicCube 2) (m : ℤ)
    (hQ : Q.scale = m+40) (r0 : ℕ) (hr : r0 ≤ 5) :
    (∀ U ∈ bankObserverRoots Q r0, U.scale ≤ m ∧ m-U.scale ≤ 5) ∧
      (bankObserverRoots Q r0).card ≤ 6*9^45 := by
  refine ⟨?_,?_⟩
  · intro U hU
    have hs := bank_observer_roots_scale Q m hQ r0 hU
    omega
  · rw [bank_observer_roots_card]
    exact (pow_le_pow_right₀ (by norm_num : (1:ℕ) ≤ 9)
      (by omega : 40+r0 ≤ 45)).trans (by omega)

theorem bank_observer_union_geometry (Q : TriadicCube 2) (m : ℤ)
    (hQ : Q.scale = m+40) (rmax : ℕ) (hr : rmax ≤ 5) :
    (∀ U ∈ bankObserverRootUnion Q rmax, U.scale ≤ m ∧ m-U.scale ≤ 5) ∧
      (bankObserverRootUnion Q rmax).card ≤ 6*9^45 := by
  classical
  refine ⟨?_,?_⟩
  · intro U hU
    obtain ⟨r0,hr0,hU⟩ := Finset.mem_biUnion.mp hU
    have hr0' : r0 ≤ 5 := by have := Finset.mem_range.mp hr0; omega
    exact (bank_observer_roots_geometry Q m hQ r0 hr0').1 U hU
  · unfold bankObserverRootUnion
    calc
      _ ≤ ∑ r0 ∈ Finset.range (rmax+1), (bankObserverRoots Q r0).card := Finset.card_biUnion_le
      _ ≤ ∑ _r0 ∈ Finset.range (rmax+1), 9^45 := by
        apply Finset.sum_le_sum
        intro r0 hr0
        rw [bank_observer_roots_card]
        have hr0' := Finset.mem_range.mp hr0
        exact pow_le_pow_right₀ (by norm_num : (1:ℕ) ≤ 9) (by omega : 40+r0 ≤ 45)
      _ = (rmax+1)*9^45 := by simp
      _ ≤ 6*9^45 := Nat.mul_le_mul_right _ (by omega : rmax+1 ≤ 6)

/-- The actual partial insertion has full strength before shell m+s,
strength sqrt(t) at that shell, and zero on the remaining finite band. -/
noncomputable def bankPartialInsertionWeights (m : ℤ) (s : ℕ) (t : ℝ) (k : ℤ) : ℝ :=
  if k < m+(s:ℤ) then 1 else if k = m+(s:ℤ) then Real.sqrt t else 0

theorem bank_partial_insertion_weights_bounds (m : ℤ) (s : ℕ) (t : ℝ) (ht : t ≤ 1) :
    ∀ k, 0 ≤ bankPartialInsertionWeights m s t k ∧ bankPartialInsertionWeights m s t k ≤ 1 := by
  intro k
  unfold bankPartialInsertionWeights
  split_ifs
  · norm_num
  · exact ⟨Real.sqrt_nonneg _, Real.sqrt_le_one.mpr ht⟩
  · norm_num

/-- These weights give the actual partial physical law, with the completed
m frame retained rather than assigning a frame to the partial law. -/
theorem bank_partial_insertion_coefficient (M : ABKModel 2) (m : ℤ)
    (s : ℕ) (hs : 1 ≤ s ∧ s ≤ 40) (t : ℝ) (ω : Cutoff.CutoffSample 2) (x : Vec 2) :
    attenuatedCoefficient M m (m+40) (bankPartialInsertionWeights m s t) ω x =
      Cutoff.coefficientCutoff M.nu (m+(s:ℤ)-1) ω x +
        Real.sqrt t • (ω.val (m+(s:ℤ))).forgetShell x := by
  classical
  have hterm (k : ℤ) : bankPartialInsertionWeights m s t k • (ω.val k).forgetShell x =
      (if k < m+(s:ℤ) then (ω.val k).forgetShell x else 0) +
        (if k = m+(s:ℤ) then Real.sqrt t • (ω.val k).forgetShell x else 0) := by
    by_cases hlt : k < m+(s:ℤ)
    · simp [bankPartialInsertionWeights, hlt, ne_of_lt hlt]
    · by_cases heq : k = m+(s:ℤ)
      · simp [bankPartialInsertionWeights, heq]
      · simp [bankPartialInsertionWeights, hlt, heq]
  have hsets : (Finset.Ioc m (m+40)).filter (fun k => k < m+(s:ℤ)) =
      Finset.Ioc m (m+(s:ℤ)-1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    omega
  have hfirst : (∑ k ∈ Finset.Ioc m (m+40),
      if k < m+(s:ℤ) then (ω.val k).forgetShell x else 0) =
        ∑ k ∈ Finset.Ioc m (m+(s:ℤ)-1), (ω.val k).forgetShell x := by
    rw [← Finset.sum_filter, hsets]
  have hmem : m+(s:ℤ) ∈ Finset.Ioc m (m+40) := by
    simp only [Finset.mem_Ioc]
    omega
  have hsum : (∑ k ∈ Finset.Ioc m (m+40),
      bankPartialInsertionWeights m s t k • (ω.val k).forgetShell x) =
        (∑ k ∈ Finset.Ioc m (m+(s:ℤ)-1), (ω.val k).forgetShell x) +
          Real.sqrt t • (ω.val (m+(s:ℤ))).forgetShell x := by
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, hfirst]
    simp only [Finset.sum_ite_eq', hmem, ite_true]
  have hc := congrArg (fun a : RegCoeffField 2 => a x)
    (Cutoff.cutoff_add_finiteShellIncrement ω (show m ≤ m+(s:ℤ)-1 by omega))
  change Cutoff.cutoff m ω x + Cutoff.finiteShellIncrement ω.val m (m+(s:ℤ)-1) x =
    Cutoff.cutoff (m+(s:ℤ)-1) ω x at hc
  rw [Cutoff.finiteShellIncrement_apply] at hc
  change Cutoff.cutoff m ω x +
    (∑ k ∈ Finset.Ioc m (m+(s:ℤ)-1), (ω.val k).forgetShell x) =
      Cutoff.cutoff (m+(s:ℤ)-1) ω x at hc
  unfold attenuatedCoefficient
  rw [hsum, Cutoff.coefficientCutoff_apply, Cutoff.coefficientCutoff_apply, ← hc]
  abel

/-- First-local bank for the exact forty-shell partial-insertion family. -/
theorem first_local_inverse_bank_partial_insertion
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (m : ℤ) (hQ : Q.scale = m+40)
    (s : ℕ) (_hs : 1 ≤ s ∧ s ≤ 40) (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hpast : ∀ n < m, nativeInductionState M h n) :
    InverseBankConclusion M .firstLocal (bankObserverRootUnion Q 5) m (m+40)
      (bankPartialInsertionWeights m s t) := by
  have hgeometry := bank_observer_union_geometry Q m hQ 5 le_rfl
  exact first_local_inverse_bank M h hM hg _ m (m+40) (by omega)
    (bankPartialInsertionWeights m s t)
    (fun k _ => bank_partial_insertion_weights_bounds m s t ht.2 k)
    hgeometry.1 hgeometry.2 hpast

end ASDExplicitGamma.Inverse
