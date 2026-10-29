module

public import ASDExplicitGamma.Inverse.StoppedGroupCorrection
public import ASDExplicitGamma.Inverse.StoppedComponentStarSupport
public import ASDExplicitGamma.Inverse.StoppedMeshHatBounds
public import ASDExplicitGamma.Triadic.DiagInterpolant
public import ASDExplicitGamma.Triadic.PlanarDirectionLinear

/-! Actual common-mesh group corrections and their weak derivatives are
supported in their component neighborhoods, with no additional collar. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization Algsuperdiff.Section3 Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Whitney ASDExplicitGamma.Triadic
noncomputable section

/-- A component node's source star belongs to that actual component's whole
touching neighborhood. Its canonical group label is derived from membership. -/
theorem stopped_group_node_star_neighborhood (M : ABKModel 2) (Q : TriadicCube 2)
    (H : ℕ) (hH : 333 ≤ H) (τ η : ℝ) (ω : Cutoff.CutoffSample 2)
    (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
      (q3PlanarMarks M (Q.scale-k) τ η) k (rootBlockStart Q k))
    (S : Set (TriadicCube 2)) (hS : S ⊆ whitneyRootPartition Q H)
    (hbad : ∀ V ∈ S, ω ∈ cellFailure M τ η V)
    (a : ℕ) (C : rootComponentGroup Q H S a)
    (z : InteriorNode (compatibleWhitneyMeshDepth H (a+1)))
    (hz : z ∈ componentMeshNodes Q _ C.val)
    (n : ℕ) (P : TriadicCube 2) (hP : P ∈ whitneyRootLayer Q H n)
    (x : Vec 2) (hx : x ∈ openCubeSet P)
    (hnear : ∀ k, |x k-diagInteriorVertex Q (compatibleWhitneyMeshDepth H (a+1)) z k| ≤
      diagMeshRadius Q (compatibleWhitneyMeshDepth H (a+1))) :
    P ∈ rootWhitneyNeighborhood Q H C.val := by
  obtain ⟨R,hR,he⟩ := C.property.1
  have ha : rootComponentLeastLayer Q H (badComponent S R)=a := by rw [← he]; exact C.property.2
  have hs := stopped_component_node_star_in_neighborhood M Q H hH τ η ω hgood S hS hbad R hR
  dsimp only at hs
  rw [ha] at hs
  have hz' : z ∈ componentMeshNodes Q (compatibleWhitneyMeshDepth H (a+1)) (badComponent S R) := by
    rwa [← he]
  rw [he]
  exact hs z hz' n P hP x hx hnear

end
end ASDExplicitGamma.Inverse
