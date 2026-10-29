module

public import ASDExplicitGamma.Inverse.StoppedBadCellLift
public import ASDExplicitGamma.Inverse.StoppedRootFineSeparation
public import Algsuperdiff.Section3.Provider.Whitney.BoundaryDistance

/-! Actual Whitney lifts use at most two generations and the same extended
bad event. Their closure-touching steps remain fine-lattice steps. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization Algsuperdiff.Section3 Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Whitney
noncomputable section

/-- Descendant closed cubes stay inside their actual parent closed cube. -/
theorem descendant_closed_cube_subset {A V : TriadicCube 2} {r : ℕ}
    (hV : V ∈ descendantsAtDepth A r) :
    Metric.closedBall (cubeCenter V) (cubeRadius V) ⊆
      Metric.closedBall (cubeCenter A) (cubeRadius A) := by
  rw [← closure_cubeSet_eq_closedBall,← closure_cubeSet_eq_closedBall]
  exact closure_mono (cubeSet_subset_of_mem_descendantsAtDepth hV)

end
end ASDExplicitGamma.Inverse
