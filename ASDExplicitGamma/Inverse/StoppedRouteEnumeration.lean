module

public import ASDExplicitGamma.Inverse.StoppedPlanarGraph

/-! A literal finite population of all planar block routes from a fixed origin. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open SimpleGraph

/-- Recursive neighbor choices enumerate all routes without a global finite
lattice box or a hidden bound on their endpoints. -/
def BlockRoutes (x : BlockSite) : ℕ → Type
  | 0 => PUnit
  | n+1 => (y : blockGraph.neighborSet x) × BlockRoutes y.val n

/-- Each route population is finite by the exact finite neighbor enumeration. -/
instance blockRoutesFintype (x : BlockSite) (n : ℕ) : Fintype (BlockRoutes x n) := by
  induction n generalizing x with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih =>
    let hLocal : ∀ y : blockGraph.neighborSet x, Fintype (BlockRoutes y.val n) := fun y => ih y.val
    exact inferInstanceAs (Fintype ((y : blockGraph.neighborSet x) × BlockRoutes y.val n))

/-- The all-route count is exactly eight to the number of edges. This slightly
larger population also covers every shortest induced path. -/
theorem block_routes_card (x : BlockSite) (n : ℕ) : Fintype.card (BlockRoutes x n) = 8^n := by
  induction n generalizing x with
  | zero =>
    change Fintype.card PUnit = 1
    exact Fintype.card_unique
  | succ n ih =>
    change Fintype.card ((y : blockGraph.neighborSet x) × BlockRoutes y.val n) = 8^(n+1)
    rw [Fintype.card_sigma]
    simp only [ih,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
      SimpleGraph.card_neighborSet_eq_degree,block_graph_degree,pow_succ]
    omega

/-- Realize each finite route by its literal graph walk and endpoint. -/
def blockRouteWalk (x : BlockSite) : (n : ℕ) → BlockRoutes x n → (y : BlockSite) × blockGraph.Walk x y
  | 0, _ => ⟨x,.nil⟩
  | n+1, r =>
    let q := blockRouteWalk r.1.val n r.2
    ⟨q.1,q.2.cons r.1.property⟩

/-- The finite route length is exact. -/
theorem block_route_walk_length (x : BlockSite) (n : ℕ) (r : BlockRoutes x n) :
    (blockRouteWalk x n r).2.length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change (blockRouteWalk r.1.val n r.2).2.length+1 = n+1
    rw [ih]

end ASDExplicitGamma.Inverse
