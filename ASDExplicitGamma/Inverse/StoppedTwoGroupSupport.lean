module

public import ASDExplicitGamma.Inverse.StoppedGroupFallback
public import ASDExplicitGamma.Inverse.StoppedGroupLayerSupport
public import ASDExplicitGamma.Inverse.StoppedSupportedL2Bounds
public import ASDExplicitGamma.Inverse.StoppedGroupDecay
public import ASDExplicitGamma.Inverse.CompatibleGluing
public import ASDExplicitGamma.Inverse.StoppedSeriesRepresentative

/-! Inside one actual Whitney cell, only its own and the preceding canonical
mesh groups can contribute to the whole-root midpoint correction. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3 Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Whitney
noncomputable section

/-- Actual fine cells determine their source layer uniquely. -/
theorem root_whitney_layer_unique (Q : TriadicCube 2) (H n m : ℕ) {P : TriadicCube 2}
    (hn : P ∈ whitneyRootLayer Q H n) (hm : P ∈ whitneyRootLayer Q H m) : n=m := by
  have hsn := root_whitney_layer_scale Q H n hn
  have hsm := root_whitney_layer_scale Q H m hm
  rcases lt_trichotomy n m with hlt | heq | hgt
  · have hp := whitney_profile_mono H hlt.le
    omega
  · exact heq
  · have hp := whitney_profile_mono H hgt.le
    omega

variable (M : ABKModel 2) (Q : TriadicCube 2) (H : ℕ) (hH : 333 ≤ H)
  (τ η : ℝ) (ω : Cutoff.CutoffSample 2)
  (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
    (q3PlanarMarks M (Q.scale-k) τ η) k (rootBlockStart Q k))
  (S : Set (TriadicCube 2)) (hS : S ⊆ whitneyRootPartition Q H)
  (hbad : ∀ V ∈ S, ω ∈ cellFailure M τ η V)

end
end ASDExplicitGamma.Inverse
