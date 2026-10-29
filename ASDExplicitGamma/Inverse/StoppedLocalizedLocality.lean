module

public import ASDExplicitGamma.Inverse.StoppedLocalObservationGeometry
public import ASDExplicitGamma.Inverse.StoppedLocalOccupation
public import ASDExplicitGamma.Inverse.StoppedQ3Independence
public import ASDExplicitGamma.Inverse.StoppedRealDiameter

/-! The actual localized diameter observes the full raw family in its doubled physical region. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.BadEvents
open scoped ENNReal
noncomputable section

/-- An activation meeting the inspection box observes all its raw sites,
including the outside sites, inside the doubled physical region. -/
theorem retained_activation_physical_subset (j : ℤ) (M n : ℕ) (hn : n < M)
    (x y : BlockSite)
    (hy : y ∈ blockCube (fun d => x d-((3^M:ℕ):ℤ)) (2*3^M+1)) :
    physicalActivationRegion j n (alignedCubeIndex (3^(n+1)) y) ⊆ localizedPhysicalRegion j M x := by
  intro p hp
  obtain ⟨z,hz,hp⟩ := Set.mem_iUnion₂.mp hp
  have hside : (3^(n+1):ℕ) ≤ 3^M := pow_le_pow_right₀ (by norm_num : (1:ℕ) ≤ 3) (by omega)
  have hraw := (mem_cube_sites _ _ _).mp hz
  have hbox := raw_site_in_double_inspection_box x y z (3^M) (3^(n+1)) (by positivity) hside hy hraw
  exact physical_block_region_subset j _ z _ hbox hp

/-- Every localized occupation event belongs to one common cutoff-local
sigma-field, even though individual retained activations have outside raw sites. -/
theorem q3_localized_occupied_local (A : ABKModel 2) (j : ℤ) (τ η : ℝ)
    (M : ℕ) (x y : BlockSite) :
    MeasurableSet[Cutoff.cutoffSampleLocalSigma A (j+40+M) (localizedPhysicalRegion j M x)]
      {ω | y ∈ localizedOccupied (q3PlanarMarks A j τ η) M (3^M) x ω} := by
  let localizedInfo : MeasurableSpace (Cutoff.CutoffSample 2) :=
    Cutoff.cutoffSampleLocalSigma A (j+40+M) (localizedPhysicalRegion j M x)
  by_cases hy : y ∈ blockCube (fun d => x d-((3^M:ℕ):ℤ)) (2*3^M+1)
  · have hL : MeasurableSet ((q3PlanarMarks A j τ η).localMark y) :=
      (cutoffSampleLocalSigma_mono A (by omega : j+40 ≤ j+40+M)
        (inspection_block_physical_subset j M x y hy)) _ (q3_local_mark_local A j τ η y)
    have hA (n : ℕ) (hn : n < M) : MeasurableSet
        (positiveActivation (q3PlanarMarks A j τ η) n (alignedCubeIndex (3^(n+1)) y)) :=
      (cutoffSampleLocalSigma_mono A (by omega : j+40+(n+1) ≤ j+40+M)
        (retained_activation_physical_subset j M n hn x y hy)) _
          (q3_positive_activation_local A j τ η n _)
    have ho := occupied_through_site_measurable_of_family (q3PlanarMarks A j τ η) M y hL hA
    simpa only [localizedOccupied,Set.mem_inter_iff,hy,and_true] using! ho
  · simp only [localizedOccupied,Set.mem_inter_iff,hy,and_false,Set.ofPred_false,MeasurableSet.empty]

/-- The actual localized extended diameter is measurable in the complete
source observation field, through label j+40+M only. -/
theorem q3_localized_diameter_local (A : ABKModel 2) (j : ℤ) (τ η : ℝ)
    (M : ℕ) (x : BlockSite) :
    @Measurable (Cutoff.CutoffSample 2) ℝ≥0∞
      (Cutoff.cutoffSampleLocalSigma A (j+40+M) (localizedPhysicalRegion j M x)) _
      (localizedDiameterField (q3PlanarMarks A j τ η) M (3^M) x) := by
  let localizedInfo : MeasurableSpace (Cutoff.CutoffSample 2) :=
    Cutoff.cutoffSampleLocalSigma A (j+40+M) (localizedPhysicalRegion j M x)
  exact diameter_field_measurable _ (q3_localized_occupied_local A j τ η M x)
    (fun _ _ => MeasurableSet.empty) x

/-- The real source field retains the same completed local information. -/
theorem q3_real_localized_diameter_local (A : ABKModel 2) (j : ℤ) (τ η : ℝ)
    (M : ℕ) (x : BlockSite) :
    @Measurable (Cutoff.CutoffSample 2) ℝ
      (Cutoff.cutoffSampleLocalSigma A (j+40+M) (localizedPhysicalRegion j M x)) _
      (realLocalizedDiameterField (q3PlanarMarks A j τ η) M (3^M) x) :=
  (q3_localized_diameter_local A j τ η M x).ennreal_toReal

end
end ASDExplicitGamma.Inverse
