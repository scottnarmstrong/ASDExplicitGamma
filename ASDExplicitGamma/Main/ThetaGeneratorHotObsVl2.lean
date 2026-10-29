module

public import ASDExplicitGamma.Main.ThetaGeneratorHotTrialExpectationsDrop
public import ASDExplicitGamma.Main.ThetaGeneratorMixedBridgeLocalCore
public import ASDExplicitGamma.Main.ThetaGeneratorEnvelopeA
public import ASDExplicitGamma.Main.LoadsAndSlopes
public import ASDExplicitGamma.Main.SourcePrefixGates
public import ASDExplicitGamma.Native.SourceRowsInterface
public import ASDExplicitGamma.Inverse.SourceInterfaceRows
public import ASDExplicitGamma.Scalar.MixedSourceCarriers
public import ASDExplicitGamma.Inverse.MixedBridgeConclusion
public import ASDExplicitGamma.Inverse.MixedBridgeLocalTheta
public import ASDExplicitGamma.Inverse.MixedBridgeLocalWeightedTheta
public import ASDExplicitGamma.Inverse.MixedBridgeSharpSlope
public import ASDExplicitGamma.Numerics.Native.Source5
public import ASDExplicitGamma.Main.AffineObserverFrame
public import ASDExplicitGamma.Inverse.MixedBridgeLocalCorrector
public import ASDExplicitGamma.Inverse.ParentGapRare
public import ASDExplicitGamma.Inverse.RawTraceHistory
public import ASDExplicitGamma.Native.OldSignedParentWeakBudgets
public import ASDExplicitGamma.Native.OldSignedSourceInverseSplit
public import ASDExplicitGamma.Main.ThetaGeneratorHotObsLocalRows
public import ASDExplicitGamma.Inverse.MixedBridgeLocal

/-! Observer-root version of the unweighted local first-corrector moment of the hot
trial: `E V_U^2 <= xi - betaOld * a <= xi` for every cell `U` of the observer tiling
`descendantsAtDepth (originCube 2 (m + hobs)) (hobs + 5)`, and for the tiling average. -/

@[expose] public section

namespace ASDExplicitGamma.Main

attribute [local irreducible] Homogenization.descendantsAtDepth

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Model
open ASDExplicitGamma.Native ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic

noncomputable section

/-- Every depth-`hobs+5` cell of the observer root `originCube 2 (m+hobs)` (`hobs ≤ 40`) is a
bank observer root of depth five. -/
theorem hot_obs_cell_mem_bank_roots_Th (m : ℤ) (hobs : ℕ) (h40 : hobs ≤ 40)
    (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth (originCube 2 (m + hobs)) (hobs + 5)) :
    U ∈ bankObserverRoots (originCube 2 (m + 40)) 5 := by
  have hparent : originCube 2 (m + hobs) ∈
      descendantsAtDepth (originCube 2 (m + 40)) (40 - hobs) := by
    have h := originCube_mem_descendantsAtDepth' 2 (m + 40) (40 - hobs)
    have e : m + 40 - ((40 - hobs : ℕ) : ℤ) = m + hobs := by
      push_cast [Nat.cast_sub h40]
      ring
    rwa [e] at h
  have hdepth := mem_descendantsAtDepth_add hparent hU
  have e2 : 40 - hobs + (hobs + 5) = 40 + 5 := by omega
  rw [e2] at hdepth
  exact hdepth

/-- Every cell of the observer tiling has scale `m - 5`. -/
theorem hot_obs_cell_scale_Th (m : ℤ) (hobs : ℕ) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth (originCube 2 (m + hobs)) (hobs + 5)) :
    U.scale = m - ((5 : ℕ) : ℤ) := by
  have hs := scale_eq_sub_of_mem_descendantsAtDepth hU
  simp only [originCube] at hs
  rw [hs]
  push_cast
  ring

/-- The observer tiling average of the local first-corrector squares. -/
def mainHotObsVl2_Th (M : ABKModel 2) (m : ℤ) (hobs : ℕ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  descendantsAverage (originCube 2 (m + hobs)) (hobs + 5)
    (fun U => mixedBridgeVLocal_Th M m U t ω ^ 2)

end

end ASDExplicitGamma.Main
