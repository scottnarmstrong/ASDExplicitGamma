module

public import ASDExplicitGamma.Inverse.StoppedClusterDiameter

/-! The monotone localization uses actual retained in-box component diameters. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open SimpleGraph MeasureTheory
open scoped ENNReal
noncomputable section

/-- Encoding a literal site occupation as local marks, with no additional
positive activations. This allows reuse of the actual component API. -/
def siteEventMarks {Ω : Type*} (O : Ω → Set BlockSite) : PlanarMarks Ω where
  localMark x := {ω | x ∈ O ω}
  positiveMark _ _ := ∅

theorem site_event_marks_occupied {Ω : Type*} (O : Ω → Set BlockSite) (ω : Ω) :
    markedOccupied (siteEventMarks O) ω = O ω := by
  ext x
  constructor
  · intro hx
    rcases hx with hx | ⟨n,i,hi,_⟩
    · exact hx
    · obtain ⟨y,_,hy⟩ := Set.mem_iUnion₂.mp hi
      exact False.elim hy
  · intro hx
    exact Or.inl hx

/-- All retained aligned activations are evaluated on their full raw
populations, and only then is the occupied graph restricted to the box. -/
def localizedOccupied {Ω : Type*} (B : PlanarMarks Ω) (M N : ℕ)
    (x : BlockSite) (ω : Ω) : Set BlockSite :=
  markedOccupiedThrough B M ω ∩ blockCube (fun d => x d-(N:ℤ)) (2*N+1)

/-- The literal source Z_N. A component reaching the box boundary keeps its
actual diameter, so no artificial maximal box diameter is inserted. -/
def localizedDiameterField {Ω : Type*} (B : PlanarMarks Ω) (M N : ℕ)
    (x : BlockSite) (ω : Ω) : ℝ≥0∞ :=
  diameterField (siteEventMarks (localizedOccupied B M N x)) ω x

/-- Actual occupied component membership is monotone under occupation inclusion. -/
theorem cluster_sites_mono {Ω : Type*} {B C : PlanarMarks Ω} (ω : Ω)
    (hBC : markedOccupied B ω ⊆ markedOccupied C ω) (x : BlockSite) :
    clusterSites B ω x ⊆ clusterSites C ω x := by
  rintro y ⟨hx,hy,hr⟩
  exact ⟨hBC hx,hBC hy,hr.map (blockGraph.induceHomOfLE hBC).toHom⟩

/-- The extended component diameter is monotone without any finiteness premise. -/
theorem cluster_diameter_mono {Ω : Type*} {B C : PlanarMarks Ω} (ω : Ω)
    (hBC : markedOccupied B ω ⊆ markedOccupied C ω) (x : BlockSite) :
    clusterDiameter B ω x ≤ clusterDiameter C ω x := by
  classical
  apply iSup_le
  intro y
  apply iSup_le
  intro z
  apply le_iSup_of_le y
  apply le_iSup_of_le z
  have hm := cluster_sites_mono ω hBC x
  by_cases hpair : y ∈ clusterSites B ω x ∧ z ∈ clusterSites B ω x
  · have hpair' : y ∈ clusterSites C ω x ∧ z ∈ clusterSites C ω x := ⟨hm hpair.1,hm hpair.2⟩
    simp only [Set.indicator,Set.mem_ofPred_eq,hpair.1,hpair.2,hpair'.1,hpair'.2,true_and,ite_true,le_refl]
  · simp only [Set.indicator,Set.mem_ofPred_eq,hpair,ite_false,zero_le]

/-- Finite-neighborhood diameter maxima preserve occupation inclusion. -/
theorem diameter_field_mono {Ω : Type*} {B C : PlanarMarks Ω} (ω : Ω)
    (hBC : markedOccupied B ω ⊆ markedOccupied C ω) (x : BlockSite) :
    diameterField B ω x ≤ diameterField C ω x := by
  change (diameterRoots x).sup (fun y => clusterDiameter B ω y) ≤
    (diameterRoots x).sup (fun y => clusterDiameter C ω y)
  apply Finset.sup_le
  intro y hy
  exact (cluster_diameter_mono (B := B) (C := C) ω hBC y).trans
    (Finset.le_sup (f := fun z => clusterDiameter C ω z) hy)

/-- Every retained occupied site is occupied in the complete marked field. -/
theorem occupied_through_subset {Ω : Type*} (B : PlanarMarks Ω) (M : ℕ) (ω : Ω) :
    markedOccupiedThrough B M ω ⊆ markedOccupied B ω := by
  rintro y hy
  rcases hy with hy | ⟨n,_,i,hi,hy⟩
  · exact Or.inl hy
  · exact Or.inr ⟨n,i,hi,hy⟩

/-- Localization is pointwise below the actual full diameter field. This is
the rare-moment monotonicity needed by the variance term in Bernstein. -/
theorem localized_diameter_field_le {Ω : Type*} (B : PlanarMarks Ω) (M N : ℕ)
    (x : BlockSite) (ω : Ω) :
    localizedDiameterField B M N x ω ≤ diameterField B ω x := by
  have hO : markedOccupied (siteEventMarks (localizedOccupied B M N x)) ω ⊆
      markedOccupied B ω := by
    rw [site_event_marks_occupied]
    exact fun _ hy => occupied_through_subset B M ω hy.1
  exact diameter_field_mono (B := siteEventMarks (localizedOccupied B M N x))
    (C := B) ω hO x

/-- Every localized component is contained in the finite inspection box. -/
theorem localized_cluster_subset_box {Ω : Type*} (B : PlanarMarks Ω) (M N : ℕ)
    (x y : BlockSite) (ω : Ω) :
    clusterSites (siteEventMarks (localizedOccupied B M N x)) ω y ⊆
      blockCube (fun d => x d-(N:ℤ)) (2*N+1) := by
  rintro z ⟨_,hz,_⟩
  rw [site_event_marks_occupied] at hz
  exact hz.2

end
end ASDExplicitGamma.Inverse
