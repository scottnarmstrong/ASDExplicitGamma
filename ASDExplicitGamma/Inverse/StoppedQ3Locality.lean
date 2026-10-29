module

public import ASDExplicitGamma.Inverse.StoppedQ3Marks
public import ASDExplicitGamma.Inverse.ClippedMatrixHistoryLocal

/-! Complete local information for the genuine parent-and-descendant marks. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian Algsuperdiff.Section3.Provider.BadEvents
noncomputable section

/-- All old-history failures in one source block read only the complete
cutoff information below the parent's buffered label. -/
theorem q3_local_mark_local (M : ABKModel 2) (j : ℤ) (τ η : ℝ) (x : BlockSite) :
    MeasurableSet[Cutoff.cutoffSampleLocalSigma M (j+40) (physicalBlockRegion j x 1)]
      ((q3PlanarMarks M j τ η).localMark x) := by
  let localInfo : MeasurableSpace (Cutoff.CutoffSample 2) :=
    Cutoff.cutoffSampleLocalSigma M (j+40) (physicalBlockRegion j x 1)
  have hi (i : WavePlanarElementaryIndex) : MeasurableSet {ω : Cutoff.CutoffSample 2 |
      ENNReal.ofReal τ < clippedCellRawHistory M ((elementaryCube j x i).scale+40)
        (elementaryCube j x i) ω} := by
    have hQU : cubeSet (elementaryCube j x i) ⊆ physicalBlockRegion j x 1 :=
      (cubeSet_subset_of_mem_descendantsAtDepth (elementary_cube_mem j x i)).trans
        (buffered_parent_contained j x (i.1,i.2.1))
    have hl : (elementaryCube j x i).scale+40 ≤ j+40 :=
      add_le_add (elementary_cube_scale_le j x i) le_rfl
    have hm := (clipped_raw_history_local_measurable M _ _ hQU).mono
      (cutoffSampleLocalSigma_mono M hl (Set.Subset.refl _)) le_rfl
    exact measurableSet_lt measurable_const hm
  simpa only [q3PlanarMarks,elementaryHistoryFailure,Set.iUnion_ofPred] using MeasurableSet.iUnion hi

/-- Each positive family uses all smaller-shell restrictions in the same
physical block, observed through the parent's largest fresh label. -/
theorem q3_positive_mark_local (M : ABKModel 2) (j : ℤ) (τ η : ℝ)
    (n : ℕ) (x : BlockSite) :
    MeasurableSet[Cutoff.cutoffSampleLocalSigma M (j+40+(n+1)) (physicalBlockRegion j x 1)]
      ((q3PlanarMarks M j τ η).positiveMark n x) := by
  apply wave_gate_family_local
  · intro i
    have hh := elementary_cube_scale_le j x i
    omega
  · intro i
    exact zpow_pos (by norm_num) _
  · exact elementary_closed_square_contained j x

end
end ASDExplicitGamma.Inverse
