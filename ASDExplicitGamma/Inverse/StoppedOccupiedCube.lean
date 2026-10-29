module

public import ASDExplicitGamma.Inverse.StoppedCubeGeodesic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Subwalks

/-! A shortest occupied path spends at most side vertices between visits to an active cube. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open SimpleGraph

/-- A wholly occupied cube gives an actual path in the full occupied graph,
with its literal side-minus-one length bound. -/
theorem occupied_cube_walk {O : Set BlockSite} (a : BlockSite) (side : ℕ)
    (hO : blockCube a side ⊆ O) (x y : O)
    (hx : x.val ∈ blockCube a side) (hy : y.val ∈ blockCube a side) :
    ∃ p : (blockGraph.induce O).Walk x y, p.length ≤ side-1 := by
  let f : (blockGraph.induce (blockCube a side)) →g (blockGraph.induce O) :=
    { toFun := fun z => ⟨z.val,hO z.property⟩
      map_rel' := fun h => h }
  have hN (d : Fin 2) : |y.val d-x.val d| ≤ ((side-1:ℕ):ℤ) := by
    have hl := hx d
    have hr := hy d
    rw [abs_le]
    constructor <;> omega
  obtain ⟨p,hp⟩ := cube_walk_length_le a side (side-1) ⟨x.val,hx⟩ ⟨y.val,hy⟩ hN
  exact ⟨p.map f,by simpa only [Walk.length_map] using hp⟩

/-- The entire first-to-last visit span has at most side vertices. This is
where shortestness and complete occupation of the enlarged cube are used. -/
theorem shortest_occupied_cube_span {O : Set BlockSite} {u v : O}
    (p : (blockGraph.induce O).Walk u v)
    (hp : p.length = (blockGraph.induce O).dist u v)
    (a : BlockSite) (side : ℕ) (hO : blockCube a side ⊆ O)
    (i j : ℕ) (hij : i ≤ j) (hj : j ≤ p.length)
    (hiCube : (p.getVert i).val ∈ blockCube a side)
    (hjCube : (p.getVert j).val ∈ blockCube a side) :
    j-i+1 ≤ side := by
  let q := (p.drop i).take (j-i)
  have hqsub : q.IsSubwalk p :=
    ((p.drop i).isSubwalk_take (j-i)).trans (p.isSubwalk_drop i)
  have hqLen : q.length = j-i := by
    simp only [q,Walk.take_length,Walk.drop_length]
    omega
  have he : (p.drop i).getVert (j-i) = p.getVert j := by
    rw [Walk.drop_getVert]
    congr 1
    omega
  have hdist := length_eq_dist_of_subwalk hp hqsub
  change q.length = (blockGraph.induce O).dist (p.getVert i) ((p.drop i).getVert (j-i)) at hdist
  rw [hqLen,he] at hdist
  obtain ⟨r,hr⟩ := occupied_cube_walk a side hO (p.getVert i) (p.getVert j) hiCube hjCube
  have hb := (SimpleGraph.dist_le r).trans hr
  rw [← hdist] at hb
  have hs : 0 < side := by
    have hh := hiCube 0
    omega
  omega

end ASDExplicitGamma.Inverse
