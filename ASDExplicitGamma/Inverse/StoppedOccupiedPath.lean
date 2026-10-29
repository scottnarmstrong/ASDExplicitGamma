module

public import ASDExplicitGamma.Inverse.StoppedPlanarGraph
public import ASDExplicitGamma.Inverse.StoppedShortestPath

/-! Spatial separation of the actual shortest occupied planar paths. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open SimpleGraph

/-- Distinct vertices in one parity class of an actual shortest occupied path
are separated by more than one block coordinate. This is the geometry used
with whole restriction-field independence. -/
theorem occupied_shortest_path_parity {O : Set BlockSite} {u v : O}
    (p : (blockGraph.induce O).Walk u v)
    (hp : p.length = (blockGraph.induce O).dist u v)
    (i j : Fin (p.length+1)) (hne : i ≠ j) (hparity : i.val%2 = j.val%2) :
    ∃ d, 1 < |(p.getVert j.val).val d-(p.getVert i.val).val d| := by
  have hsep := shortest_path_parity_separated p hp i j hne hparity
  have hpath := p.isPath_of_length_eq_dist hp
  have hn : p.getVert i.val ≠ p.getVert j.val := by
    intro he
    apply hne
    have hi : i.val ≤ p.length := Nat.le_of_lt_succ i.isLt
    have hj : j.val ≤ p.length := Nat.le_of_lt_succ j.isLt
    exact Fin.ext (hpath.getVert_injOn hi hj he)
  by_contra! hclose
  apply hsep
  change blockGraph.Adj (p.getVert i.val).val (p.getVert j.val).val
  exact ⟨fun he => hn (Subtype.ext he),hclose⟩

end ASDExplicitGamma.Inverse
