module

public import ASDExplicitGamma.Inverse.StoppedRootWhitneyLift

/-! A source-cell lift at a fixed root depth is its unique genuine ancestor.
This identifies all component-local Z witnesses on the same current cell. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization Algsuperdiff.Section3.Provider.Whitney

/-- The actual source lift is independent of which touching component was
used to produce its coarser ancestor. -/
theorem root_whitney_lift_unique {Q P A B : TriadicCube 2} {h : ℕ}
    (hA : RootWhitneyLift Q h P A) (hB : RootWhitneyLift Q h P B) : A=B := by
  by_contra hne
  have hd := pairwiseDisjoint_descendantsAtDepth Q h hA.1 hB.1 hne
  obtain ⟨r,hr,hPA⟩ := hA.2
  obtain ⟨s,hs,hPB⟩ := hB.2
  have hx := cubeCenter_mem_cubeSet P
  exact Set.disjoint_left.mp hd
    (cubeSet_subset_of_mem_descendantsAtDepth hPA hx)
    (cubeSet_subset_of_mem_descendantsAtDepth hPB hx)

end ASDExplicitGamma.Inverse
