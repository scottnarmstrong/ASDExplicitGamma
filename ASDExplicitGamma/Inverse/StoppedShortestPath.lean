module

public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
public import Lean.Elab.Tactic.Omega

/-! The actual shortest-path separation used for independent planar parity classes. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open SimpleGraph

/-- A shortest occupied path has no edge joining nonconsecutive vertices.
The graph here can be the occupied induced subgraph, so this does not assume
that every point of a surrounding box is occupied. -/
theorem shortest_path_nonconsecutive {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hp : p.length = G.dist u v) (i j : ℕ)
    (hj : j ≤ p.length) (hij : i+1 < j) : ¬ G.Adj (p.getVert i) (p.getVert j) := by
  intro hadj
  let q := ((p.take i).append hadj.toWalk).append (p.drop j)
  have hlen : q.length = min i p.length+1+(p.length-j) := by
    simp only [q, Walk.length_append, Walk.take_length, Walk.drop_length, SimpleGraph.Adj.length_toWalk]
  have hdist := G.dist_le q
  rw [← hp,hlen] at hdist
  omega

/-- Each parity class of a shortest path is separated in the graph. -/
theorem shortest_path_parity_separated {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hp : p.length = G.dist u v) (i j : Fin (p.length+1))
    (hne : i ≠ j) (hparity : i.val%2 = j.val%2) :
    ¬ G.Adj (p.getVert i.val) (p.getVert j.val) := by
  have hn : i.val ≠ j.val := fun h => hne (Fin.ext h)
  by_cases hij : i.val < j.val
  · exact shortest_path_nonconsecutive p hp i.val j.val (by omega) (by omega)
  · intro hadj
    exact shortest_path_nonconsecutive p hp j.val i.val (by omega) (by omega) hadj.symm

end ASDExplicitGamma.Inverse
