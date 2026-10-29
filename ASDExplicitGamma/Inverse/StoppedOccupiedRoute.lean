module

public import ASDExplicitGamma.Inverse.StoppedRouteEnumeration
public import ASDExplicitGamma.Inverse.StoppedOccupiedPath
public import ASDExplicitGamma.Inverse.StoppedMarkControl

/-! Encode actual shortest occupied paths in a deterministic finite route population. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open SimpleGraph

/-- All vertex locations of a fixed finite candidate route, independent of the sample. -/
def blockRouteVertices (x : BlockSite) (n : ℕ) (r : BlockRoutes x n) : Fin (n+1) → BlockSite :=
  fun k => (blockRouteWalk x n r).2.getVert k.val

/-- Forget only the occupation proofs, retaining every actual vertex choice. -/
def occupiedWalkRoute {O : Set BlockSite} {x y : O}
    (p : (blockGraph.induce O).Walk x y) : BlockRoutes x.val p.length :=
  match p with
  | .nil => PUnit.unit
  | @Walk.cons _ _ _ z _ hadj q => ⟨⟨z.val,hadj⟩,occupiedWalkRoute q⟩

/-- Every location is preserved, including all endpoint and zero-length cases. -/
theorem occupied_route_vertex {O : Set BlockSite} {x y : O}
    (p : (blockGraph.induce O).Walk x y) (k : ℕ) :
    (blockRouteWalk x.val p.length (occupiedWalkRoute p)).2.getVert k = (p.getVert k).val := by
  induction p generalizing k with
  | nil => rfl
  | @cons x y z h p ih =>
    cases k with
    | zero => rfl
    | succ k =>
      change (blockRouteWalk y.val p.length (occupiedWalkRoute p)).2.getVert k = (p.getVert k).val
      exact ih k

/-- Every actual shortest occupied route has the deterministic spatial parity
separation required by the local restriction-independence input. -/
theorem occupied_route_parity_separated {O : Set BlockSite} {x y : O}
    (p : (blockGraph.induce O).Walk x y) (hp : p.length = (blockGraph.induce O).dist x y) :
    RouteParitySeparated (blockRouteVertices x.val p.length (occupiedWalkRoute p)) := by
  intro i j hne hparity
  simpa only [blockRouteVertices,occupied_route_vertex] using!
    occupied_shortest_path_parity p hp i j hne hparity

end ASDExplicitGamma.Inverse
