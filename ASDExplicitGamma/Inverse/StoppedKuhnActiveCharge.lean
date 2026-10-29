module

public import ASDExplicitGamma.Inverse.StoppedKuhnGradientCharge
public import ASDExplicitGamma.Inverse.StoppedActiveResolution

/-! Literal source active-cell payment for the common midpoint map. Every
closure-touching active cell supplies its own diameter-at-least-one charge. -/
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

theorem stopped_kuhn_gradient_ae_active_charge
    (hfinite : ∀ j ≤ Q.scale-(H:ℤ), ∀ z,
      diameterField (q3PlanarMarks M j τ η) ω z ≠ ∞) :
    ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q), ∀ (n : ℕ) (P : TriadicCube 2),
      P ∈ whitneyRootLayer Q H n → (∃ V ∈ S, CubeTouch P V) → x ∈ openCubeSet P →
      ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (stoppedKuhnGradient M Q H hH τ η ω hgood S hS hbad x)‖^2 ≤
        (planarGradientCharge 40+1)*(∑ e : Fin 3, (layerResolutionDiameter M Q H τ η n e ω x)^2) := by
  filter_upwards [stopped_kuhn_gradient_ae_three_resolution_charge M Q H hH τ η ω hgood S hS hbad hfinite] with x hx
  intro n P hP hactive hxP
  apply (hx n P hP hxP).trans
  exact active_three_resolution_charge 40 _
    (stopped_active_resolution_one M Q H hH τ η ω hgood S hS hbad hfinite n P hP hactive x ((openCubeSet_subset_cubeSet P) hxP))

end
end ASDExplicitGamma.Inverse
