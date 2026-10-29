module

public import ASDExplicitGamma.Inverse.WhitneyRootLayerGeometry

/-! Whole closed Whitney cells lie strictly inside their physical root,
including every vertex needed by the compatible midpoint prescription. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Whitney
noncomputable section

/-- Strict interior containment includes the full closed cell, not only its
half-open realization or its center. -/
theorem root_whitney_closed_cell_interior (Q : TriadicCube 2) (H n : ℕ)
    {V : TriadicCube 2} (hV : V ∈ whitneyRootLayer Q H n) :
    Metric.closedBall (cubeCenter V) (cubeRadius V) ⊆ openCubeSet Q := by
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hV
  have hPs := whitney_scale_le Q.scale H ⟨n,hP⟩
  have hi := closedBall_subset_openCubeSet_of_not_touchesBoundary
    (mem_descendantsAtDepth_of_mem_whitneyLayer hP) (not_touchesBoundary_of_mem_whitneyLayer hP)
  intro x hx
  rw [openCubeSet_eq_translateSet_originCube_of_triadicCube,mem_translateSet_iff_sub_mem]
  apply hi
  rw [Metric.mem_closedBall,dist_eq_norm] at hx ⊢
  rw [root_translate_cube_center Q P hPs,cubeRadius_eq_zpow_div_two,root_translate_cube_scale] at hx
  rw [cubeRadius_eq_zpow_div_two]
  have he : x-triadicCubeShift Q-cubeCenter P = x-(cubeCenter P+triadicCubeShift Q) := by abel
  rwa [he]

end
end ASDExplicitGamma.Inverse
