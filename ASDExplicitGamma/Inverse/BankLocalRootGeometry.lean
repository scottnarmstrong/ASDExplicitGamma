module

public import ASDExplicitGamma.Inverse.BankObservers

/-! Local root families, with symbolic observer geometry. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse
open Homogenization Algsuperdiff.Section3

@[irreducible] noncomputable def bankLocalRoots (Q : TriadicCube 2) (rmax : ℕ) : Finset (TriadicCube 2) := by
  classical
  exact insert Q ((Finset.range (rmax+1)).biUnion (descendantsAtDepth Q))

theorem bank_local_roots_geometry (Q : TriadicCube 2) (rmax : ℕ) (hr : rmax ≤ 5) :
    (∀ U ∈ bankLocalRoots Q rmax, U.scale ≤ Q.scale ∧ Q.scale-U.scale ≤ 5) ∧
      (bankLocalRoots Q rmax).card ≤ 6*9^45 := by
  classical
  refine ⟨?_,?_⟩
  · intro U hU
    rw [bankLocalRoots] at hU
    rcases Finset.mem_insert.mp hU with rfl | hU
    · exact ⟨le_rfl,by omega⟩
    obtain ⟨r,hr',hU⟩ := Finset.mem_biUnion.mp hU
    have hs := scale_eq_sub_of_mem_descendantsAtDepth hU
    have hrr := Finset.mem_range.mp hr'
    omega
  · have hcard : ((Finset.range (rmax+1)).biUnion (descendantsAtDepth Q)).card ≤ 6*9^44 := by
      calc
        _ ≤ ∑ r ∈ Finset.range (rmax+1), (descendantsAtDepth Q r).card := Finset.card_biUnion_le
        _ ≤ ∑ _r ∈ Finset.range (rmax+1), 9^44 := by
          apply Finset.sum_le_sum
          intro r hr'
          rw [descendantsAtDepth_card,show (3^2:ℕ)=9 by norm_num]
          exact pow_le_pow_right₀ (by norm_num : (1:ℕ) ≤ 9)
            (by have := Finset.mem_range.mp hr'; omega)
        _ = (rmax+1)*9^44 := by simp
        _ ≤ 6*9^44 := Nat.mul_le_mul_right _ (by omega)
    rw [bankLocalRoots]
    exact (Finset.card_insert_le Q _).trans ((Nat.add_le_add_right hcard 1).trans (by norm_num))

theorem bank_local_roots_self (Q : TriadicCube 2) (rmax : ℕ) : Q ∈ bankLocalRoots Q rmax := by
  classical
  rw [bankLocalRoots]
  exact Finset.mem_insert_self Q _

theorem bank_member_history_le (M : ABKModel 2) (s : Finset (TriadicCube 2))
    (Q : TriadicCube 2) (hQ : Q ∈ s) (m J : ℤ) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) :
    bankRootInverseHistory Q M m J weights ω ≤ bankFiniteRootHistoryMax s M m J weights ω := by
  have hh := Finset.le_sup (s:=Finset.univ)
    (f:=fun U : ↥s => bankRootInverseHistory U.1 M m J weights ω)
    (b:=(⟨Q,hQ⟩ : ↥s)) (Finset.mem_univ (⟨Q,hQ⟩ : ↥s))
  exact hh

end ASDExplicitGamma.Inverse
