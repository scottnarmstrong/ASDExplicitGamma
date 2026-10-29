module

public import ASDExplicitGamma.Inverse.StoppedGroupSupport
public import ASDExplicitGamma.Inverse.WhitneyRootLayerCarrier

/-! A group correction and all its weak derivatives are supported in the
two actual source layers of that group, on one common spatial null set. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3 Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Whitney
noncomputable section

theorem stopped_group_neighborhood_layers (M : ABKModel 2) (Q : TriadicCube 2)
    (H : ℕ) (hH : 333 ≤ H) (τ η : ℝ) (ω : Cutoff.CutoffSample 2)
    (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
      (q3PlanarMarks M (Q.scale-k) τ η) k (rootBlockStart Q k))
    (S : Set (TriadicCube 2)) (hS : S ⊆ whitneyRootPartition Q H)
    (hbad : ∀ V ∈ S, ω ∈ cellFailure M τ η V) (a : ℕ)
    (C : rootComponentGroup Q H S a) {P : TriadicCube 2}
    (hP : P ∈ rootWhitneyNeighborhood Q H C.val) :
    P ∈ whitneyRootLayer Q H a ∨ P ∈ whitneyRootLayer Q H (a+1) := by
  obtain ⟨R,hR,he⟩ := C.property.1
  have ha : rootComponentLeastLayer Q H (badComponent S R)=a := by rw [← he]; exact C.property.2
  have ht := (stopped_component_lifted_paths M Q H hH τ η ω hgood S hS hbad R hR).2
  rw [ha] at ht
  exact ht P (by rwa [← he])

end
end ASDExplicitGamma.Inverse
