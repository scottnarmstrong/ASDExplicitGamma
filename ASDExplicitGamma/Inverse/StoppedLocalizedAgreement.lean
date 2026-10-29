module

public import ASDExplicitGamma.Inverse.StoppedClusterRestriction

/-! Localization agrees with the actual full field when components stay inside and no omitted cube fires. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open SimpleGraph
open scoped ENNReal
noncomputable section

/-- A full component meeting the radius-two neighborhood escapes inspection. -/
def localizationEscape {Ω : Type*} (B : PlanarMarks Ω) (N : ℕ) (x : BlockSite) : Set Ω :=
  {ω | ∃ y ∈ diameterRoots x, ∃ z ∈ clusterSites B ω y,
    z ∉ blockCube (fun d => x d-(N:ℤ)) (2*N+1)}

/-- Some omitted positive label activates a cube intersecting the inspection
box. Its activation still uses the full raw population, not only in-box sites. -/
def omittedActivation {Ω : Type*} (B : PlanarMarks Ω) (M N : ℕ) (x : BlockSite) : Set Ω :=
  {ω | ∃ n, M ≤ n ∧ ∃ i, ω ∈ positiveActivation B n i ∧
    ∃ z ∈ blockCube (fun d => x d-(N:ℤ)) (2*N+1),
      z ∈ blockCube (alignedCubeBase (3^(n+1)) i) (3^(n+1))}

/-- In the absence of both actual failure mechanisms, every relevant full
component is retained and the localized diameter equals the full diameter. -/
theorem localized_diameter_eq_of_no_failures {Ω : Type*} (B : PlanarMarks Ω)
    (M N : ℕ) (x : BlockSite) (ω : Ω)
    (hstay : ω ∉ localizationEscape B N x) (hhigh : ω ∉ omittedActivation B M N x) :
    localizedDiameterField B M N x ω = diameterField B ω x := by
  let C := siteEventMarks (localizedOccupied B M N x)
  have hCB : markedOccupied C ω ⊆ markedOccupied B ω := by
    rw [site_event_marks_occupied]
    exact fun _ hy => occupied_through_subset B M ω hy.1
  have hretain (y : BlockSite) (hy : y ∈ diameterRoots x) :
      clusterSites B ω y ⊆ markedOccupied C ω := by
    intro z hz
    have hbox : z ∈ blockCube (fun d => x d-(N:ℤ)) (2*N+1) := by
      by_contra hn
      exact hstay ⟨y,hy,z,hz,hn⟩
    have hocc : z ∈ markedOccupied B ω := by
      obtain ⟨_,hz,_⟩ := hz
      exact hz
    rw [site_event_marks_occupied]
    refine ⟨?_,hbox⟩
    rcases hocc with hlocal | ⟨n,i,hi,hz⟩
    · exact Or.inl hlocal
    · have hn : n < M := by
        by_contra! hn
        exact hhigh ⟨n,hn,i,hi,z,hbox,hz⟩
      exact Or.inr ⟨n,hn,i,hi,hz⟩
  change (diameterRoots x).sup (fun y => clusterDiameter C ω y) =
    (diameterRoots x).sup (fun y => clusterDiameter B ω y)
  apply Finset.sup_congr rfl
  intro y hy
  exact cluster_diameter_eq_of_sites_eq B C ω y (cluster_sites_eq_of_retained B C ω hCB y (hretain y hy))

/-- The actual localization mismatch is contained in the union of cluster
escape and omitted activation, before any probabilistic estimates. -/
theorem localized_diameter_mismatch_subset {Ω : Type*} (B : PlanarMarks Ω)
    (M N : ℕ) (x : BlockSite) :
    {ω | localizedDiameterField B M N x ω ≠ diameterField B ω x} ⊆
      localizationEscape B N x ∪ omittedActivation B M N x := by
  intro ω hω
  by_contra! hn
  have hn' : ω ∉ localizationEscape B N x ∧ ω ∉ omittedActivation B M N x := by
    simpa only [Set.mem_union,not_or] using hn
  exact hω (localized_diameter_eq_of_no_failures B M N x ω hn'.1 hn'.2)

end
end ASDExplicitGamma.Inverse
