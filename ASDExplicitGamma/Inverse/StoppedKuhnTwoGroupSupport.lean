module

public import ASDExplicitGamma.Inverse.StoppedGlobalKuhnSeries
public import ASDExplicitGamma.Inverse.StoppedTwoGroupSupport

/-! Inside one actual Whitney cell, only its own and the preceding canonical
mesh groups can contribute to the whole-root midpoint correction. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3 Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Whitney
noncomputable section

variable (M : ABKModel 2) (Q : TriadicCube 2) (H : ℕ) (hH : 333 ≤ H)
  (τ η : ℝ) (ω : Cutoff.CutoffSample 2)
  (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
    (q3PlanarMarks M (Q.scale-k) τ η) k (rootBlockStart Q k))
  (S : Set (TriadicCube 2)) (hS : S ⊆ whitneyRootPartition Q H)
  (hbad : ∀ V ∈ S, ω ∈ cellFailure M τ η V)

/-- A distant group is exactly zero in both its value and every chosen weak
derivative representative throughout the current cell's interior. -/
theorem stopped_kuhn_group_vanish_on_other_layers (i : Fin 2) (a n : ℕ)
    (P : TriadicCube 2) (hP : P ∈ whitneyRootLayer Q H n)
    (hfar : a ≠ n ∧ a+1 ≠ n) (x : Vec 2) (hx : x ∈ openCubeSet P) :
    (stoppedKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad i a).toFun x=0 ∧
      ∀ k, (stoppedKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad i a).grad x k=0 := by
  have hz : ¬ ((stoppedKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad i a).toFun x ≠ 0 ∨
      ∃ k, (stoppedKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad i a).grad x k ≠ 0) := by
    intro hv
    obtain ⟨C,hC,hPC⟩ := stopped_kuhn_group_field_support M Q H hH τ η ω hgood S hS hbad a
      (stopped_component_group_finite M Q H hH τ η ω hgood S hS hbad a)
      (fun C => stopped_component_group_nodes_nonempty M Q H hH τ η ω hgood S hS hbad a C.property)
      i n P hP x hx hv
    have hl := stopped_group_neighborhood_layers M Q H hH τ η ω hgood S hS hbad a ⟨C,hC⟩ hPC
    rcases hl with hl | hl
    · exact hfar.1 (root_whitney_layer_unique Q H a n hl hP)
    · exact hfar.2 (root_whitney_layer_unique Q H (a+1) n hl hP)
  constructor
  · by_contra hn
    exact hz (Or.inl hn)
  · intro k
    by_contra hn
    exact hz (Or.inr ⟨k,hn⟩)

end
end ASDExplicitGamma.Inverse
