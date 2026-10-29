module

public import ASDExplicitGamma.Inverse.StoppedKuhnTwoGroupSupport
public import ASDExplicitGamma.Inverse.StoppedTwoGroupRepresentative

/-! The whole-root H1 midpoint correction equals the two actually active
source groups in every Whitney interior, on one common spatial null set. -/
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

/-- Exact two-group identity for values and every weak-gradient coordinate.
No convergence or pointwise-series premise remains. -/
theorem stopped_global_kuhn_correction_ae_two_groups (i : Fin 2) :
    ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q), ∀ (n : ℕ) (P : TriadicCube 2),
      P ∈ whitneyRootLayer Q H n → x ∈ openCubeSet P →
      (stoppedGlobalKuhnCorrection M Q H hH τ η ω hgood S hS hbad i).toFun x=
        (stoppedKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad i n).toFun x+
        (stoppedKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad i (n-1)).toFun x ∧
      ∀ k, (stoppedGlobalKuhnCorrection M Q H hH τ η ω hgood S hS hbad i).grad x k=
        (stoppedKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad i n).grad x k+
        (stoppedKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad i (n-1)).grad x k := by
  filter_upwards [stopped_global_kuhn_correction_ae_hasSum M Q H hH τ η ω hgood S hS hbad i] with x hx
  intro n P hP hxP
  have hn := root_whitney_layer_pos Q H n hP
  have hv (a : ℕ) (ha : a ≠ n) (han : a+1 ≠ n) :=
    stopped_kuhn_group_vanish_on_other_layers M Q H hH τ η ω hgood S hS hbad i a n P hP ⟨ha,han⟩ x hxP
  constructor
  · exact hx.1.unique (two_group_hasSum _ n hn (fun a ha han => (hv a ha han).1))
  · intro k
    exact (hx.2 k).unique (two_group_hasSum _ n hn (fun a ha han => (hv a ha han).2 k))

end
end ASDExplicitGamma.Inverse
