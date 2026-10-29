module

public import ASDExplicitGamma.Inverse.StoppedGlobalKuhnSeries
public import ASDExplicitGamma.Inverse.StoppedGlobalKuhnMidpointMap

/-! The actual source common map equals the identity throughout every whole
Whitney cell untouched by the bad family. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ASDExplicitGamma.Triadic
open Algsuperdiff.Section3 Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Affine Algsuperdiff.Section3.Provider.Whitney
noncomputable section

variable (M : ABKModel 2) (Q : TriadicCube 2) (H : ℕ) (hH : 333 ≤ H)
  (τ η : ℝ) (ω : Cutoff.CutoffSample 2)
  (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
    (q3PlanarMarks M (Q.scale-k) τ η) k (rootBlockStart Q k))
  (S : Set (TriadicCube 2)) (hS : S ⊆ whitneyRootPartition Q H)
  (hbad : ∀ V ∈ S, ω ∈ cellFailure M τ η V)

theorem stopped_kuhn_group_zero_on_untouched (i : Fin 2) (a n : ℕ)
    (P : TriadicCube 2) (hP : P ∈ whitneyRootLayer Q H n)
    (hoff : ∀ V ∈ S, ¬ CubeTouch P V) (x : Vec 2) (hx : x ∈ openCubeSet P) :
    (stoppedKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad i a).toFun x=0 ∧
      ∀ k, (stoppedKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad i a).grad x k=0 := by
  have hn : ¬ ((stoppedKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad i a).toFun x ≠ 0 ∨
      ∃ k, (stoppedKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad i a).grad x k ≠ 0) := by
    intro hv
    obtain ⟨C,hC,hPC⟩ := stopped_kuhn_group_field_support M Q H hH τ η ω hgood S hS hbad a
      (stopped_component_group_finite M Q H hH τ η ω hgood S hS hbad a)
      (fun C => stopped_component_group_nodes_nonempty M Q H hH τ η ω hgood S hS hbad a C.property) i n P hP x hx hv
    obtain ⟨V,hVC,ht⟩ := hPC.2
    obtain ⟨R,hR,he⟩ := hC.1
    have hVS : V ∈ S := by rw [he] at hVC; exact hVC.1
    exact hoff V hVS ht
  constructor
  · by_contra h
    exact hn (Or.inl h)
  · intro k
    by_contra h
    exact hn (Or.inr ⟨k,h⟩)

theorem stopped_global_kuhn_correction_ae_untouched (i : Fin 2) :
    ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q), ∀ (n : ℕ) (P : TriadicCube 2),
      P ∈ whitneyRootLayer Q H n → (∀ V ∈ S, ¬ CubeTouch P V) → x ∈ openCubeSet P →
      (stoppedGlobalKuhnCorrection M Q H hH τ η ω hgood S hS hbad i).toFun x=0 ∧
      ∀ k, (stoppedGlobalKuhnCorrection M Q H hH τ η ω hgood S hS hbad i).grad x k=0 := by
  filter_upwards [stopped_global_kuhn_correction_ae_hasSum M Q H hH τ η ω hgood S hS hbad i] with x hx
  intro n P hP hoff hxP
  have hz (a : ℕ) := stopped_kuhn_group_zero_on_untouched M Q H hH τ η ω hgood S hS hbad i a n P hP hoff x hxP
  constructor
  · have hh := hx.1
    have he : (fun a => (stoppedKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad i a).toFun x)=fun _ => (0:ℝ) :=
      funext (fun a => (hz a).1)
    rw [he] at hh
    exact hh.unique hasSum_zero
  · intro k
    have hh := hx.2 k
    have he : (fun a => (stoppedKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad i a).grad x k)=fun _ => (0:ℝ) :=
      funext (fun a => (hz a).2 k)
    rw [he] at hh
    exact hh.unique hasSum_zero

end
end ASDExplicitGamma.Inverse
