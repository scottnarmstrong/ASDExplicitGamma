module

public import ASDExplicitGamma.Inverse.ContainedTriangleCount
public import Mathlib.Data.Nat.Choose.Cast

/-! The complete first-containment decomposition of a planar Kuhn triangle. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization

/-- First containment at depth n+1: the cube is contained but its parent is not. -/
noncomputable def triangleFirstCubes (l : ℤ) (pi : Equiv.Perm (Fin 2)) (n : ℕ) :
    Finset (TriadicCube 2) :=
  (triangleContainedCubes l pi (n + 1)).filter
    (fun R => parentCube R ∉ triangleContainedCubes l pi n)

private theorem parent_of_child_mem {A R : TriadicCube 2} (hR : R ∈ childCubes A) :
    parentCube R = A := by
  obtain ⟨digits, rfl⟩ := mem_childCubes_iff.mp hR
  exact childCube_parent A digits

/-- Every child of a contained cube stays in the same ordered-coordinate triangle. -/
theorem triangle_child_contained (l : ℤ) (pi : Equiv.Perm (Fin 2)) (n : ℕ)
    {A R : TriadicCube 2} (hA : A ∈ triangleContainedCubes l pi n)
    (hR : R ∈ childCubes A) : R ∈ triangleContainedCubes l pi (n + 1) := by
  obtain ⟨hAd, hAo⟩ := Finset.mem_filter.mp hA
  refine Finset.mem_filter.mpr ⟨mem_descendantsAtDepth_succ_iff.mpr ⟨A, hAd, hR⟩, ?_⟩
  obtain ⟨digits, rfl⟩ := mem_childCubes_iff.mp hR
  change 3 * A.index (pi 0) + (digits (pi 0) : ℤ) - 1 <
    3 * A.index (pi 1) + (digits (pi 1) : ℤ) - 1
  have h0 : (digits (pi 0) : ℤ) < 3 := by exact_mod_cast (digits (pi 0)).is_lt
  have h1 : 0 ≤ (digits (pi 1) : ℤ) := Int.natCast_nonneg _
  omega

/-- Next-depth contained cubes split into the first-contained cubes and the
nine children of every already-contained cube. -/
theorem triangle_contained_next (l : ℤ) (pi : Equiv.Perm (Fin 2)) (n : ℕ) :
    triangleContainedCubes l pi (n + 1) = triangleFirstCubes l pi n ∪
      (triangleContainedCubes l pi n).biUnion childCubes := by
  classical
  ext R
  constructor
  · intro hR
    by_cases hp : parentCube R ∈ triangleContainedCubes l pi n
    · obtain ⟨A, _, hRA⟩ := mem_descendantsAtDepth_succ_iff.mp (Finset.mem_filter.mp hR).1
      have he := parent_of_child_mem hRA
      rw [he] at hp
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨A, hp, hRA⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hR, hp⟩)
  · intro hR
    rcases Finset.mem_union.mp hR with hR | hR
    · exact (Finset.mem_filter.mp hR).1
    · obtain ⟨A, hA, hRA⟩ := Finset.mem_biUnion.mp hR
      exact triangle_child_contained l pi n hA hRA

/-- The first-contained layer does not overlap children counted previously. -/
theorem triangle_contained_next_disjoint (l : ℤ) (pi : Equiv.Perm (Fin 2)) (n : ℕ) :
    Disjoint (triangleFirstCubes l pi n) ((triangleContainedCubes l pi n).biUnion childCubes) := by
  classical
  apply Finset.disjoint_left.mpr
  intro R hR hR'
  obtain ⟨A, hA, hRA⟩ := Finset.mem_biUnion.mp hR'
  exact (Finset.mem_filter.mp hR).2 (parent_of_child_mem hRA ▸ hA)

/-- Exact first-containment cardinality, obtained from the complete contained-bin count. -/
theorem triangle_first_card (l : ℤ) (pi : Equiv.Perm (Fin 2)) (n : ℕ) :
    (triangleFirstCubes l pi n).card = 3 ^ (n + 1) := by
  classical
  have hc : (triangleContainedCubes l pi (n + 1)).card =
      (triangleFirstCubes l pi n).card + 9 * (triangleContainedCubes l pi n).card := by
    rw [triangle_contained_next, Finset.card_union_of_disjoint (triangle_contained_next_disjoint l pi n)]
    congr 1
    rw [Finset.card_biUnion]
    · simp only [childCubes_card, Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
      norm_num
      omega
    · intro A hA B hB hAB
      exact disjoint_childCubes_of_ne hAB
  rw [triangle_contained_card, triangle_contained_card] at hc
  have hR := congrArg (fun a : ℕ => (a : ℝ)) hc
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_choose_two, Nat.cast_pow] at hR
  have he : ((triangleFirstCubes l pi n).card : ℝ) = (3 : ℝ) ^ (n + 1) := by
    rw [pow_succ (3 : ℝ) n] at hR ⊢
    nlinarith only [hR]
  exact_mod_cast he

end ASDExplicitGamma.Inverse
