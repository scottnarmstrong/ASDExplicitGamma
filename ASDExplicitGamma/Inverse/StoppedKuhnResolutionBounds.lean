module

public import ASDExplicitGamma.Inverse.StoppedResolutionFields
public import ASDExplicitGamma.Inverse.StoppedKuhnGroupDiameterGradient
public import ASDExplicitGamma.Inverse.StoppedGlobalKuhnCorrection

/-! Actual source group gradients charged to one of the three physical
pointwise diameter fields on the current Whitney layer. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ASDExplicitGamma.Triadic
open Algsuperdiff.Section3 Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Affine Algsuperdiff.Section3.Provider.Whitney
open scoped ENNReal
noncomputable section

variable (M : ABKModel 2) (Q : TriadicCube 2) (H : ℕ) (hH : 333 ≤ H)
  (τ η : ℝ) (ω : Cutoff.CutoffSample 2)
  (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
    (q3PlanarMarks M (Q.scale-k) τ η) k (rootBlockStart Q k))
  (S : Set (TriadicCube 2)) (hS : S ⊆ whitneyRootPartition Q H)
  (hbad : ∀ V ∈ S, ω ∈ cellFailure M τ η V)

theorem stopped_kuhn_group_resolution_bound
    (hfinite : ∀ j ≤ Q.scale-(H:ℤ), ∀ z,
      diameterField (q3PlanarMarks M j τ η) ω z ≠ ∞)
    (a n : ℕ) (han : a ≤ n) (hna : n ≤ a+1) (e : Fin 3)
    (hlabel : Q.scale-(compatibleWhitneyMeshDepth H a:ℤ)=layerResolutionLabel Q H n e)
    (P : TriadicCube 2) (hP : P ∈ whitneyRootLayer Q H n)
    (x : Vec 2) (hxP : x ∈ openCubeSet P)
    (U : KuhnCell 2) (hU : U ∈ rootKuhnMesh Q (compatibleWhitneyMeshDepth H (a+1)))
    (hxU : x ∈ U.openCarrier) (i k : Fin 2) :
    |(stoppedKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad i a).grad x k| ≤
      18*(3:ℝ)^40*layerResolutionDiameter M Q H τ η n e ω x := by
  obtain ⟨T,hPT⟩ := root_whitney_two_layer_lift Q H a n han hna hP
  have hj : Q.scale-((a+whitneyProfile H a:ℕ):ℤ) ≤ Q.scale-(H:ℤ) := by
    change Q.scale-(compatibleWhitneyMeshDepth H a:ℤ) ≤ _
    rw [hlabel]
    exact layer_resolution_protected Q H n e
  have hf := hfinite _ hj (fineBlockIndex T.index)
  have hb := root_whitney_lift_physical_block_index hPT ((openCubeSet_subset_cubeSet P) hxP)
  have hh := stopped_kuhn_group_gradient_diameter_bound M Q H hH τ η ω hgood S hS hbad a
    (stopped_component_group_finite M Q H hH τ η ω hgood S hS hbad a)
    (fun C => stopped_component_group_nodes_nonempty M Q H hH τ η ω hgood S hS hbad a C.property)
    i k n P T hP hPT hf x hxP U hU hxU
  change |(stoppedKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad i a).grad x k| ≤
    18*(3:ℝ)^40*realDiameterField
      (q3PlanarMarks M (Q.scale-(compatibleWhitneyMeshDepth H a:ℤ)) τ η)
      (fineBlockIndex T.index) ω at hh
  have hz : layerResolutionDiameter M Q H τ η n e ω x=
      realDiameterField (q3PlanarMarks M (Q.scale-(compatibleWhitneyMeshDepth H a:ℤ)) τ η)
        (fineBlockIndex T.index) ω := by
    dsimp only [layerResolutionDiameter]
    rw [← hlabel]
    change physicalBlockIndex (Q.scale-(compatibleWhitneyMeshDepth H a:ℤ)) x=fineBlockIndex T.index at hb
    rw [hb]
  exact hh.trans_eq (congrArg (fun z : ℝ => 18*(3:ℝ)^40*z) hz.symm)

end
end ASDExplicitGamma.Inverse
