module

public import ASDExplicitGamma.Inverse.ContainedTriangleCover

/-! Disjointness across every first-containment depth. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization

private theorem first_cubes_disjoint_of_lt (l : ℤ) (pi : Equiv.Perm (Fin 2))
    {n m : ℕ} (hnm : n < m) {R S : TriadicCube 2}
    (hR : R ∈ triangleFirstCubes l pi n) (hS : S ∈ triangleFirstCubes l pi m) :
    Disjoint (cubeSet R) (cubeSet S) := by
  apply Set.disjoint_left.mpr
  intro x hxR hxS
  obtain ⟨B, hB, hSB⟩ := mem_descendantsAtDepth_succ_iff.mp
    (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1
  have hpar : parentCube S = B := by
    obtain ⟨digits, rfl⟩ := mem_childCubes_iff.mp hSB
    exact childCube_parent B digits
  have hm : n + 1 + (m - (n + 1)) = m := by omega
  obtain ⟨A, hA, hBA⟩ := exists_descendant_ancestor_at_depth (n + 1) (m - (n + 1))
    (by rw [hm]; exact hB)
  have hxB := cubeSet_subset_of_mem_childCubes hSB hxS
  have hxA := cubeSet_subset_of_mem_descendantsAtDepth hBA hxB
  have hAR : A = R := by
    by_contra hne
    exact Set.disjoint_left.mp (pairwiseDisjoint_descendantsAtDepth (originCube 2 l) (n + 1)
      hA (Finset.mem_filter.mp (Finset.mem_filter.mp hR).1).1 hne) hxA hxR
  subst A
  have hc := triangle_descendant_contained l pi (n + 1) (m - (n + 1))
    (Finset.mem_filter.mp hR).1 hBA
  rw [hm] at hc
  exact (Finset.mem_filter.mp hS).2 (hpar ▸ hc)

/-- All first-contained cubes are pairwise disjoint, including cubes at different depths. -/
theorem triangle_partition_disjoint (l : ℤ) (pi : Equiv.Perm (Fin 2)) :
    (triangleCubePartition l pi).PairwiseDisjoint cubeSet := by
  intro R hR S hS hne
  obtain ⟨n, hn⟩ := hR
  obtain ⟨m, hm⟩ := hS
  rcases lt_trichotomy n m with hlt | he | hgt
  · exact first_cubes_disjoint_of_lt l pi hlt hn hm
  · subst m
    exact pairwiseDisjoint_descendantsAtDepth (originCube 2 l) (n + 1)
      (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
      (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).1 hne
  · exact (first_cubes_disjoint_of_lt l pi hgt hm hn).symm

end ASDExplicitGamma.Inverse
