module

public import ASDExplicitGamma.Inverse.StoppedLocalizedMeasurable

/-! A site's retained occupation reads precisely its unique aligned activation cube at each label. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory
noncomputable section

theorem occupied_through_site_iff {Ω : Type*} (B : PlanarMarks Ω) (M : ℕ)
    (ω : Ω) (x : BlockSite) :
    x ∈ markedOccupiedThrough B M ω ↔ ω ∈ B.localMark x ∨
      ∃ n < M, ω ∈ positiveActivation B n (alignedCubeIndex (3^(n+1)) x) := by
  constructor
  · rintro (h | ⟨n,hn,i,hi,hx⟩)
    · exact Or.inl h
    · have he := (aligned_cube_index_iff (3^(n+1)) (by positivity) x i).mpr hx
      exact Or.inr ⟨n,hn,by simpa only [he] using hi⟩
  · rintro (h | ⟨n,hn,hi⟩)
    · exact Or.inl h
    · exact Or.inr ⟨n,hn,_,hi,mem_own_aligned_cube _ (by positivity) x⟩

/-- Only the finite retained local family is needed for this site's
measurability; all other spatial mark events may use larger sigma-fields. -/
theorem occupied_through_site_measurable_of_family {Ω : Type*} [MeasurableSpace Ω]
    (B : PlanarMarks Ω) (M : ℕ) (x : BlockSite) (hL : MeasurableSet (B.localMark x))
    (hA : ∀ n < M, MeasurableSet (positiveActivation B n (alignedCubeIndex (3^(n+1)) x))) :
    MeasurableSet {ω | x ∈ markedOccupiedThrough B M ω} := by
  have he : {ω | x ∈ markedOccupiedThrough B M ω} = B.localMark x ∪
      ⋃ n : ℕ, ⋃ _hn : n < M, positiveActivation B n (alignedCubeIndex (3^(n+1)) x) := by
    ext ω
    rw [Set.mem_union]
    simp only [Set.mem_iUnion,Set.mem_ofPred_eq,occupied_through_site_iff]
    constructor
    · rintro (h | ⟨n,hn,hi⟩)
      · exact Or.inl h
      · exact Or.inr ⟨n,hn,hi⟩
    · rintro (h | ⟨n,hn,hi⟩)
      · exact Or.inl h
      · exact Or.inr ⟨n,hn,hi⟩
  rw [he]
  exact hL.union (MeasurableSet.iUnion (fun n => MeasurableSet.iUnion (hA n)))

end
end ASDExplicitGamma.Inverse
