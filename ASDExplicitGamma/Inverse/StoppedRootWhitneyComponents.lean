module

public import ASDExplicitGamma.Inverse.StoppedRootWhitneyChain

/-! Two-layer confinement and finiteness of the actual q3 bad Whitney
components and their complete closure-touching neighborhoods. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3 Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Whitney ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
noncomputable section

/-- Complete closure-touching neighborhood in the actual physical root. -/
def rootWhitneyNeighborhood (Q : TriadicCube 2) (H : ℕ) (C : Set (TriadicCube 2)) :
    Set (TriadicCube 2) := {D | D ∈ whitneyRootPartition Q H ∧ ∃ V ∈ C, CubeTouch D V}

/-- The complete actual bad-cell family at the source Whitney profile. -/
def rootBadWhitneyCells (M : ABKModel 2) (Q : TriadicCube 2) (H : ℕ) (τ η : ℝ)
    (ω : Cutoff.CutoffSample 2) : Set (TriadicCube 2) :=
  {V | V ∈ whitneyRootPartition Q H ∧ ω ∈ cellFailure M τ η V}

end
end ASDExplicitGamma.Inverse
