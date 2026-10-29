module

public import ASDExplicitGamma.Inverse.BridgeObservables
public import ASDExplicitGamma.Inverse.ParentGapCenteredDepth
public import ASDExplicitGamma.Model.Cutoff
public import Algsuperdiff.Section3.Provider.ErrorComparison.CubeMonotonicity

/-! Small structural adapters for the centered parent cube and its actual
observer family. -/

@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
  Algsuperdiff.Section3.Provider.ErrorComparison

attribute [local irreducible] Homogenization.descendantsAtDepth

/-- The parent cube is a member of the observer family by the zero-offset
case of the structural centered-cube induction. -/
theorem mixed_bridge_parent_cube_mem_observer (m : ℤ) :
    originCube 2 m ∈ mixedBridgeObserverSourceRoots m := by
  change originCube 2 m ∈ (Finset.range 6).biUnion
    (fun r => descendantsAtDepth (originCube 2 (m + 40)) (40 + r))
  exact Finset.mem_biUnion.mpr
    ⟨0, Finset.mem_range.mpr (by omega),
      originCube_mem_descendantsAtOffset 2 m 40⟩

/-- The fixed parent coefficient is elliptic on its own completed cube,
transferred from the containing observer cube via the public depth geometry. -/
theorem partialInserted_parent_cube_elliptic
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    IsEllipticFieldOn M.nu
      (((2 : ℝ) * 2 * (Model.partialInsertedEntryBound M (m + 40) m ω) ^ 2 +
        M.nu ^ 2) / M.nu)
      (openCubeSet (originCube 2 m))
      (Model.partialInsertedCoefficient M m t ω).toFun := by
  have hdesc : originCube 2 m ∈
      descendantsAtDepth (originCube 2 (m + 40)) 40 :=
    originCube_mem_descendantsAtOffset 2 m 40
  exact Model.partialInsertedCoefficient_isEllipticFieldOn M (m + 40) m ω
    ⟨ht.1, ht.2⟩ (measurableSet_openCubeSet (originCube 2 m))
    (openCubeSet_subset_of_mem_descendantsAtDepth hdesc)

end ASDExplicitGamma.Inverse
