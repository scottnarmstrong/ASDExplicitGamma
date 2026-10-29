module

public import ASDExplicitGamma.Inverse.StoppedResolutionFields
public import ASDExplicitGamma.Inverse.StoppedNeighborComponentSpan
public import ASDExplicitGamma.Inverse.StoppedTwoGroupSupport

/-! A whole active Whitney cell pays at least one in one of the three actual
physical diameter fields. This includes closure-touching cells. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ASDExplicitGamma.Triadic
open Algsuperdiff.Section3 Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Whitney
open scoped ENNReal
noncomputable section

variable (M : ABKModel 2) (Q : TriadicCube 2) (H : ℕ) (hH : 333 ≤ H)
  (τ η : ℝ) (ω : Cutoff.CutoffSample 2)
  (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
    (q3PlanarMarks M (Q.scale-k) τ η) k (rootBlockStart Q k))
  (S : Set (TriadicCube 2)) (hS : S ⊆ whitneyRootPartition Q H)
  (hbad : ∀ V ∈ S, ω ∈ cellFailure M τ η V)

include hH hgood hS hbad in
theorem stopped_active_resolution_one
    (hfinite : ∀ j ≤ Q.scale-(H:ℤ), ∀ z,
      diameterField (q3PlanarMarks M j τ η) ω z ≠ ∞)
    (n : ℕ) (P : TriadicCube 2) (hP : P ∈ whitneyRootLayer Q H n)
    (hactive : ∃ V ∈ S, CubeTouch P V) (x : Vec 2) (hxP : x ∈ cubeSet P) :
    ∃ e : Fin 3, 1 ≤ layerResolutionDiameter M Q H τ η n e ω x := by
  obtain ⟨V,hVS,ht⟩ := hactive
  let C := badComponent S V
  let a := rootComponentLeastLayer Q H C
  let base := compatibleWhitneyMeshDepth H a
  have hPC : P ∈ rootWhitneyNeighborhood Q H C :=
    ⟨(root_partition_iff_layer Q H P).mpr ⟨n,hP⟩,V,self_mem_badComponent hVS,ht⟩
  have hh := stopped_neighbor_component_span M Q H hH τ η ω hgood S hS hbad V hVS P hPC
  obtain ⟨T,hPT,hspan⟩ := hh
  change RootWhitneyLift Q base P T at hPT
  have hprotected : Q.scale-(base:ℤ) ≤ Q.scale-(H:ℤ) := by
    unfold base compatibleWhitneyMeshDepth whitneyProfile
    omega
  have hf : diameterField (q3PlanarMarks M (Q.scale-(base:ℤ)) τ η) ω (fineBlockIndex T.index) ≠ ∞ :=
    hfinite _ hprotected _
  have hz := (hspan hf).1
  change 1 ≤ realDiameterField (q3PlanarMarks M (Q.scale-(base:ℤ)) τ η) (fineBlockIndex T.index) ω at hz
  have hb := root_whitney_lift_physical_block_index hPT hxP
  have hl := (stopped_component_lifted_paths M Q H hH τ η ω hgood S hS hbad V hVS).2 P hPC
  change P ∈ whitneyRootLayer Q H a ∨ P ∈ whitneyRootLayer Q H (a+1) at hl
  rcases hl with hl | hl
  · have hn := root_whitney_layer_unique Q H n a hP hl
    refine ⟨0,?_⟩
    have he : layerResolutionDiameter M Q H τ η n 0 ω x=
        realDiameterField (q3PlanarMarks M (Q.scale-(base:ℤ)) τ η) (fineBlockIndex T.index) ω := by
      dsimp only [layerResolutionDiameter]
      have hj : layerResolutionLabel Q H n 0=Q.scale-(base:ℤ) := by
        simp only [layerResolutionLabel,Fin.val_zero,Nat.cast_zero,add_zero,hn,base]
      rw [hj,hb]
    exact he ▸ hz
  · have hn := root_whitney_layer_unique Q H n (a+1) hP hl
    refine ⟨layerPreviousResolution H n,?_⟩
    have he : layerResolutionDiameter M Q H τ η n (layerPreviousResolution H n) ω x=
        realDiameterField (q3PlanarMarks M (Q.scale-(base:ℤ)) τ η) (fineBlockIndex T.index) ω := by
      dsimp only [layerResolutionDiameter]
      have hj : layerResolutionLabel Q H n (layerPreviousResolution H n)=Q.scale-(base:ℤ) := by
        rw [layer_previous_resolution_label]
        have ha : n-1=a := by omega
        rw [ha]
      rw [hj,hb]
    exact he ▸ hz

end
end ASDExplicitGamma.Inverse
