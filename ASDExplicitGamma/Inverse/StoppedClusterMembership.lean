module

public import ASDExplicitGamma.Inverse.StoppedFiniteClusters
public import ASDExplicitGamma.Inverse.StoppedMarkedMeasurable

/-! Countable route descriptions of actual component membership. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open SimpleGraph MeasureTheory
noncomputable section

/-- Component membership retains its exact endpoint in the fixed-route
representation. The random occupied graph introduces no measurability premise. -/
theorem cluster_sites_route_iff {Ω : Type*} (B : PlanarMarks Ω) (ω : Ω)
    (x y : BlockSite) :
    y ∈ clusterSites B ω x ↔ ∃ n, ∃ r : BlockRoutes x n,
      (∀ k : Fin (n+1), blockRouteVertices x n r k ∈ markedOccupied B ω) ∧
      blockRouteVertices x n r ⟨n,Nat.lt_succ_self n⟩ = y := by
  constructor
  · rintro ⟨hx,hy,⟨p⟩⟩
    refine ⟨p.length,occupiedWalkRoute p,?_,?_⟩
    · intro k
      have he : blockRouteVertices x p.length (occupiedWalkRoute p) k = (p.getVert k.val).val :=
        occupied_route_vertex p k.val
      rw [he]
      exact (p.getVert k.val).property
    · exact (occupied_route_vertex p p.length).trans (congrArg Subtype.val p.getVert_length)
  · rintro ⟨n,r,ho,he⟩
    let Q := blockRouteWalk x n r
    let p := Q.2
    have hlen : p.length = n := block_route_walk_length x n r
    have hs : ∀ z ∈ p.support, z ∈ markedOccupied B ω := by
      intro z hz
      obtain ⟨k,hk,hkl⟩ := Walk.mem_support_iff_exists_getVert.mp hz
      have hocc := ho ⟨k,by omega⟩
      change p.getVert k ∈ markedOccupied B ω at hocc
      simpa only [hk] using hocc
    have hlast : blockRouteVertices x n r ⟨n,Nat.lt_succ_self n⟩ = Q.1 := by
      change p.getVert n = Q.1
      rw [← hlen,Walk.getVert_length]
    have hQ : Q.1 = y := hlast.symm.trans he
    rw [← hQ]
    exact ⟨hs x p.start_mem_support,hs Q.1 p.end_mem_support,
      ⟨p.induce (markedOccupied B ω) hs⟩⟩

/-- Membership of a fixed site in a fixed root's actual component is measurable. -/
theorem cluster_sites_mem_measurable {Ω : Type*} [MeasurableSpace Ω]
    (B : PlanarMarks Ω) (hL : ∀ x, MeasurableSet (B.localMark x))
    (hP : ∀ n x, MeasurableSet (B.positiveMark n x)) (x y : BlockSite) :
    MeasurableSet {ω | y ∈ clusterSites B ω x} := by
  have he : {ω | y ∈ clusterSites B ω x} = ⋃ n : ℕ, ⋃ r : BlockRoutes x n,
      {ω | (∀ k : Fin (n+1), blockRouteVertices x n r k ∈ markedOccupied B ω) ∧
        blockRouteVertices x n r ⟨n,Nat.lt_succ_self n⟩ = y} := by
    ext ω
    simp only [Set.mem_iUnion,Set.mem_ofPred_eq,cluster_sites_route_iff]
  rw [he]
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.iUnion
  intro r
  by_cases he : blockRouteVertices x n r ⟨n,Nat.lt_succ_self n⟩ = y
  · simpa only [he,and_true] using route_occupied_measurable B hL hP x n r
  · simp only [he,and_false,Set.ofPred_false,MeasurableSet.empty]

end
end ASDExplicitGamma.Inverse
