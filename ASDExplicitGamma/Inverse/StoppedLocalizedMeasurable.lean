module

public import ASDExplicitGamma.Inverse.StoppedLocalizedDiameter

/-! Measurability of the literal retained in-box occupation and diameter. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory
noncomputable section

theorem occupied_through_site_measurable {Ω : Type*} [MeasurableSpace Ω]
    (B : PlanarMarks Ω) (hL : ∀ x, MeasurableSet (B.localMark x))
    (hP : ∀ n x, MeasurableSet (B.positiveMark n x)) (M : ℕ) (x : BlockSite) :
    MeasurableSet {ω | x ∈ markedOccupiedThrough B M ω} := by
  have he : {ω | x ∈ markedOccupiedThrough B M ω} = B.localMark x ∪
      ⋃ n : ℕ, ⋃ _hn : n < M, ⋃ i : BlockSite,
        {ω | ω ∈ positiveActivation B n i ∧
          x ∈ blockCube (alignedCubeBase (3^(n+1)) i) (3^(n+1))} := by
    ext ω
    simp only [Set.mem_union,Set.mem_iUnion,Set.mem_ofPred_eq,markedOccupiedThrough]
    constructor
    · rintro (h | ⟨n,hn,i,hi,hx⟩)
      · exact Or.inl h
      · exact Or.inr ⟨n,hn,i,hi,hx⟩
    · rintro (h | ⟨n,hn,i,hi,hx⟩)
      · exact Or.inl h
      · exact Or.inr ⟨n,hn,i,hi,hx⟩
  rw [he]
  apply (hL x).union
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.iUnion
  intro _
  apply MeasurableSet.iUnion
  intro i
  by_cases hx : x ∈ blockCube (alignedCubeBase (3^(n+1)) i) (3^(n+1))
  · simpa only [hx,and_true,Set.ofPred_mem_eq,positiveActivation,cubeActivation] using
      MeasurableSet.iUnion (fun y => MeasurableSet.iUnion (fun _hy => hP n y))
  · simp only [hx,and_false,Set.ofPred_false,MeasurableSet.empty]

/-- Restricting the graph to the inspection box is performed after retaining
all raw sites of the activating cubes, including their sites outside the box. -/
theorem localized_occupied_site_measurable {Ω : Type*} [MeasurableSpace Ω]
    (B : PlanarMarks Ω) (hL : ∀ x, MeasurableSet (B.localMark x))
    (hP : ∀ n x, MeasurableSet (B.positiveMark n x)) (M N : ℕ) (x y : BlockSite) :
    MeasurableSet {ω | y ∈ localizedOccupied B M N x ω} := by
  by_cases hy : y ∈ blockCube (fun d => x d-(N:ℤ)) (2*N+1)
  · simpa only [localizedOccupied,Set.mem_inter_iff,hy,and_true] using
      occupied_through_site_measurable B hL hP M y
  · simp only [localizedOccupied,Set.mem_inter_iff,hy,and_false,Set.ofPred_false,MeasurableSet.empty]

/-- The genuine localized diameter field is measurable on the original
probability space without a finite-energy or an independence assumption. -/
theorem localized_diameter_field_measurable {Ω : Type*} [MeasurableSpace Ω]
    (B : PlanarMarks Ω) (hL : ∀ x, MeasurableSet (B.localMark x))
    (hP : ∀ n x, MeasurableSet (B.positiveMark n x)) (M N : ℕ) (x : BlockSite) :
    Measurable (localizedDiameterField B M N x) :=
  diameter_field_measurable _ (localized_occupied_site_measurable B hL hP M N x)
    (fun _ _ => MeasurableSet.empty) x

end
end ASDExplicitGamma.Inverse
