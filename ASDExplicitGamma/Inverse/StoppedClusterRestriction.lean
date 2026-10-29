module

public import ASDExplicitGamma.Inverse.StoppedLocalizedDiameter

/-! Restricting occupation leaves every wholly retained actual component unchanged. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open SimpleGraph
open scoped ENNReal
noncomputable section

/-- Every vertex on an occupied walk belongs to its actual root component. -/
theorem occupied_walk_support_in_component {Ω : Type*} (B : PlanarMarks Ω) (ω : Ω)
    {x y : markedOccupied B ω} (p : (blockGraph.induce (markedOccupied B ω)).Walk x y)
    {z : markedOccupied B ω} (hz : z ∈ p.support) : z.val ∈ clusterSites B ω x.val := by
  obtain ⟨k,hk,_⟩ := Walk.mem_support_iff_exists_getVert.mp hz
  refine ⟨x.property,z.property,?_⟩
  rw [← hk]
  exact (p.take k).reachable

/-- If a full component is contained in retained occupation, restriction
preserves the component exactly, not only its radius upper bound. -/
theorem cluster_sites_eq_of_retained {Ω : Type*} (B C : PlanarMarks Ω) (ω : Ω)
    (hCB : markedOccupied C ω ⊆ markedOccupied B ω) (x : BlockSite)
    (hretain : clusterSites B ω x ⊆ markedOccupied C ω) :
    clusterSites C ω x = clusterSites B ω x := by
  apply Set.Subset.antisymm (cluster_sites_mono ω hCB x)
  rintro y ⟨hx,hy,⟨p⟩⟩
  let p0 := p.map (Embedding.induce (markedOccupied B ω)).toHom
  have hs : ∀ z ∈ p0.support, z ∈ markedOccupied C ω := by
    intro z hz
    change z ∈ (p.map (Embedding.induce (markedOccupied B ω)).toHom).support at hz
    rw [Walk.support_map] at hz
    obtain ⟨z',hz',he⟩ := List.mem_map.mp hz
    apply hretain
    rw [← he]
    exact occupied_walk_support_in_component B ω p hz'
  exact ⟨hs x p0.start_mem_support,hs y p0.end_mem_support,
    (p0.induce (markedOccupied C ω) hs).reachable⟩

/-- Identical actual components give identical extended diameter values. -/
theorem cluster_diameter_eq_of_sites_eq {Ω : Type*} (B C : PlanarMarks Ω) (ω : Ω)
    (x : BlockSite) (he : clusterSites C ω x = clusterSites B ω x) :
    clusterDiameter C ω x = clusterDiameter B ω x := by
  classical
  apply iSup_congr
  intro y
  apply iSup_congr
  intro z
  have hi : (y ∈ clusterSites C ω x ∧ z ∈ clusterSites C ω x) ↔
      (y ∈ clusterSites B ω x ∧ z ∈ clusterSites B ω x) :=
    and_congr (Set.ext_iff.mp he y) (Set.ext_iff.mp he z)
  by_cases hp : y ∈ clusterSites C ω x ∧ z ∈ clusterSites C ω x
  · have hp' := hi.mp hp
    simp only [Set.indicator,Set.mem_ofPred_eq,hp.1,hp.2,hp'.1,hp'.2,true_and,ite_true]
  · have hp' : ¬ (y ∈ clusterSites B ω x ∧ z ∈ clusterSites B ω x) := fun h => hp (hi.mpr h)
    simp only [Set.indicator,Set.mem_ofPred_eq,hp,hp',ite_false]

end
end ASDExplicitGamma.Inverse
