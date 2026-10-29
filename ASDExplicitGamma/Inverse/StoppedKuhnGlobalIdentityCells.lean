module

public import ASDExplicitGamma.Inverse.StoppedKuhnIdentityCells

/-! The source common coordinate map is the identity, with identity gradient,
on every whole untouched Whitney cell. -/
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

theorem stopped_global_kuhn_midpoint_ae_identity_cells (i : Fin 2) :
    ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q), ∀ (n : ℕ) (P : TriadicCube 2),
      P ∈ whitneyRootLayer Q H n → (∀ V ∈ S, ¬ CubeTouch P V) → x ∈ openCubeSet P →
      (stoppedKuhnMidpointCoordinate M Q H hH τ η ω hgood S hS hbad i).toFun x=x i ∧
      ∀ k, (stoppedKuhnMidpointCoordinate M Q H hH τ η ω hgood S hS hbad i).grad x k=basisVec i k := by
  filter_upwards [stopped_global_kuhn_correction_ae_untouched M Q H hH τ η ω hgood S hS hbad i] with x hx
  intro n P hP hoff hxP
  obtain ⟨hv,hg⟩ := hx n P hP hoff hxP
  constructor
  · change (diagAffineLinear Q (basisVec i)).toFun x+
      (stoppedGlobalKuhnCorrection M Q H hH τ η ω hgood S hS hbad i).toFun x=x i
    rw [hv,add_zero]
    exact vecDot_basisVec_left i x
  · intro k
    change (diagAffineLinear Q (basisVec i)).grad x k+
      (stoppedGlobalKuhnCorrection M Q H hH τ η ω hgood S hS hbad i).grad x k=basisVec i k
    rw [hg k,add_zero]
    rfl

end
end ASDExplicitGamma.Inverse
