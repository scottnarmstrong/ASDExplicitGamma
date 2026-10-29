module

public import ASDExplicitGamma.Inverse.StoppedOccupiedCube
public import Mathlib.Order.Interval.Finset.Fin

/-! Exact finite counts of the shortest path vertices charged to one active cube. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open SimpleGraph

/-- The actual indices at which a fixed path visits a specified cube. -/
noncomputable def pathCubeVisits {O : Set BlockSite} {u v : O}
    (p : (blockGraph.induce O).Walk u v) (a : BlockSite) (side : ℕ) : Finset (Fin (p.length+1)) := by
  classical
  exact Finset.univ.filter (fun i => (p.getVert i.val).val ∈ blockCube a side)

/-- Each active cube is charged at most its literal side, even when the path
enters, exits and re-enters. First and last visits bound all intermediate ones. -/
theorem shortest_cube_visit_card {O : Set BlockSite} {u v : O}
    (p : (blockGraph.induce O).Walk u v)
    (hp : p.length = (blockGraph.induce O).dist u v)
    (a : BlockSite) (side : ℕ) (hO : blockCube a side ⊆ O) :
    (pathCubeVisits p a side).card ≤ side := by
  classical
  let A := pathCubeVisits p a side
  by_cases hA : A.Nonempty
  · let i := A.min' hA
    let j := A.max' hA
    have hi : i ∈ A := A.min'_mem hA
    have hj : j ∈ A := A.max'_mem hA
    have hsub : A ⊆ Finset.Icc i j := by
      intro k hk
      exact Finset.mem_Icc.mpr ⟨A.min'_le k hk,A.le_max' k hk⟩
    have hij : i.val ≤ j.val := A.min'_le j hj
    have hvi : (p.getVert i.val).val ∈ blockCube a side := by
      simpa only [A,pathCubeVisits,Finset.mem_filter,Finset.mem_univ,true_and] using! hi
    have hvj : (p.getVert j.val).val ∈ blockCube a side := by
      simpa only [A,pathCubeVisits,Finset.mem_filter,Finset.mem_univ,true_and] using! hj
    have hspan := shortest_occupied_cube_span p hp a side hO i.val j.val hij
      (Nat.le_of_lt_succ j.isLt) hvi hvj
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Icc] at hcard
    change A.card ≤ side
    omega
  · have he : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    change A.card ≤ side
    rw [he]
    exact Nat.zero_le _

end ASDExplicitGamma.Inverse
