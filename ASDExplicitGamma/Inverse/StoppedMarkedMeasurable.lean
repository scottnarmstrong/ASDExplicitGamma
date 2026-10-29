module

public import ASDExplicitGamma.Inverse.StoppedOccupiedRoute
public import ASDExplicitGamma.Inverse.StoppedClusterReach

/-! Genuine measurability of the actual marked occupation and connected-component radius events. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory SimpleGraph
noncomputable section

/-- Actual occupation of one site is a measurable countable union of raw
activation observations, with no measurable-cluster premise. -/
theorem occupied_site_measurable {Ω : Type*} [MeasurableSpace Ω]
    (B : PlanarMarks Ω) (hL : ∀ x, MeasurableSet (B.localMark x))
    (hP : ∀ n x, MeasurableSet (B.positiveMark n x)) (x : BlockSite) :
    MeasurableSet {ω | x ∈ markedOccupied B ω} := by
  have hA (n : ℕ) (i : BlockSite) : MeasurableSet {ω | ω ∈ positiveActivation B n i ∧
      x ∈ blockCube (alignedCubeBase (3^(n+1)) i) (3^(n+1))} := by
    by_cases hx : x ∈ blockCube (alignedCubeBase (3^(n+1)) i) (3^(n+1))
    · simpa only [hx,and_true,Set.ofPred_mem_eq] using positive_activation_measurable B hP n i
    · simp only [hx,and_false,Set.ofPred_false,MeasurableSet.empty]
  have hpos : MeasurableSet {ω | ∃ n i, ω ∈ positiveActivation B n i ∧
      x ∈ blockCube (alignedCubeBase (3^(n+1)) i) (3^(n+1))} := by
    simpa only [Set.iUnion_ofPred] using MeasurableSet.iUnion (fun n => MeasurableSet.iUnion (fun i => hA n i))
  exact (hL x).union hpos

/-- Occupation of every vertex of a fixed candidate route is measurable. -/
theorem route_occupied_measurable {Ω : Type*} [MeasurableSpace Ω]
    (B : PlanarMarks Ω) (hL : ∀ x, MeasurableSet (B.localMark x))
    (hP : ∀ n x, MeasurableSet (B.positiveMark n x))
    (x : BlockSite) (n : ℕ) (r : BlockRoutes x n) :
    MeasurableSet {ω | ∀ k : Fin (n+1), blockRouteVertices x n r k ∈ markedOccupied B ω} := by
  simpa only [Set.iInter_ofPred] using MeasurableSet.iInter
    (fun k : Fin (n+1) => occupied_site_measurable B hL hP (blockRouteVertices x n r k))

/-- Reachability has a countable fixed-route description, so it requires no
measurability assumption on sample-dependent occupied graph witnesses. -/
theorem cluster_reaches_route_iff {Ω : Type*} (B : PlanarMarks Ω) (ω : Ω)
    (x : BlockSite) (R : ℕ) :
    ω ∈ clusterReaches B x R ↔ ∃ n, ∃ r : BlockRoutes x n,
      (∀ k : Fin (n+1), blockRouteVertices x n r k ∈ markedOccupied B ω) ∧
      ∃ d, (R:ℤ) ≤ |blockRouteVertices x n r ⟨n,Nat.lt_succ_self n⟩ d-x d| := by
  constructor
  · rintro ⟨hx,y,hr,d,hd⟩
    obtain ⟨p⟩ := hr
    refine ⟨p.length,occupiedWalkRoute p,?_,d,?_⟩
    · intro k
      have he : blockRouteVertices x p.length (occupiedWalkRoute p) k = (p.getVert k.val).val :=
        occupied_route_vertex p k.val
      rw [he]
      exact (p.getVert k.val).property
    · have he : blockRouteVertices x p.length (occupiedWalkRoute p) ⟨p.length,Nat.lt_succ_self _⟩ = y.val := by
        exact (occupied_route_vertex p p.length).trans (congrArg Subtype.val p.getVert_length)
      rw [he]
      exact hd
  · rintro ⟨n,r,ho,d,hd⟩
    let Q := blockRouteWalk x n r
    let p := Q.2
    have hlen : p.length = n := block_route_walk_length x n r
    have hs : ∀ z ∈ p.support, z ∈ markedOccupied B ω := by
      intro z hz
      obtain ⟨k,hk,hkl⟩ := Walk.mem_support_iff_exists_getVert.mp hz
      have hocc := ho ⟨k,by omega⟩
      change p.getVert k ∈ markedOccupied B ω at hocc
      simpa only [hk] using hocc
    have he : blockRouteVertices x n r ⟨n,Nat.lt_succ_self n⟩ = Q.1 := by
      change p.getVert n = Q.1
      rw [← hlen,Walk.getVert_length]
    rw [he] at hd
    exact ⟨hs x p.start_mem_support,⟨Q.1,hs Q.1 p.end_mem_support⟩,⟨p.induce (markedOccupied B ω) hs⟩,d,hd⟩

/-- The actual component radius event is genuinely measurable in the original
sample information, even though its shortest path witness is selected later. -/
theorem cluster_reaches_measurable {Ω : Type*} [MeasurableSpace Ω]
    (B : PlanarMarks Ω) (hL : ∀ x, MeasurableSet (B.localMark x))
    (hP : ∀ n x, MeasurableSet (B.positiveMark n x)) (x : BlockSite) (R : ℕ) :
    MeasurableSet (clusterReaches B x R) := by
  have he : clusterReaches B x R = ⋃ n : ℕ, ⋃ r : BlockRoutes x n,
      {ω | (∀ k : Fin (n+1), blockRouteVertices x n r k ∈ markedOccupied B ω) ∧
        ∃ d, (R:ℤ) ≤ |blockRouteVertices x n r ⟨n,Nat.lt_succ_self n⟩ d-x d|} := by
    ext ω
    simp only [Set.mem_iUnion,Set.mem_ofPred_eq,cluster_reaches_route_iff]
  rw [he]
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.iUnion
  intro r
  by_cases hdist : ∃ d, (R:ℤ) ≤ |blockRouteVertices x n r ⟨n,Nat.lt_succ_self n⟩ d-x d|
  · simpa only [hdist,and_true] using route_occupied_measurable B hL hP x n r
  · simp only [hdist,and_false,Set.ofPred_false,MeasurableSet.empty]

end
end ASDExplicitGamma.Inverse
