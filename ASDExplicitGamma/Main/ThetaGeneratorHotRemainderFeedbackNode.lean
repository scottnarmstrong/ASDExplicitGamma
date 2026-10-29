module

public import ASDExplicitGamma.Main.ThetaGeneratorHotFeedbackPathwise
public import ASDExplicitGamma.Main.ThetaGeneratorHotObsSplit
public import ASDExplicitGamma.Main.ThetaGeneratorHotESourceSquareNode
public import ASDExplicitGamma.Main.ThetaGeneratorHotTrialExpectationsSplit
public import ASDExplicitGamma.Main.ThetaGeneratorHotObsDrop
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
public import ASDExplicitGamma.Main.ThetaGeneratorHotRemainderFeedbackMoments

/-! Node MA-E-REMAINDER-FEEDBACK for the hot-patched trial at the observer root
`Q' = originCube 2 (m + hobs)` (`1 ≤ hobs ≤ 40`): the actual-law expectation of the `R'` feedback
group (`2 * ∑ feedbackSource`) is at most `2 k_d (63/50) (√2 β d + z r_ec)`. The row uses the
inverse histories `B_U ≤ B*` of the NEW global variable only through the cell histories of the
feedback bill, and the OLD proxy `Θ` only as the weight of the reciprocal-error row. -/

@[expose] public section

namespace ASDExplicitGamma.Main

attribute [local irreducible] Homogenization.descendantsAtDepth

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Model
open ASDExplicitGamma.Native ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
open ASDExplicitGamma.Variational ASDExplicitGamma.Response

noncomputable section

/-- Pathwise comparison of the RMS reciprocal error with the OLD proxy average. -/
theorem hot_reciprocal_rms_le_theta_Th (M : ABKModel 2) (hγ : M.gamma ≤ gammaZero) (m : ℤ)
    (hobs : ℕ) (h40 : hobs ≤ 40) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (ω : Cutoff.CutoffSample 2) :
    mainHotReciprocalRms_Th M m hobs t ω ≤
      Real.sqrt (2 * descendantsAverage (originCube 2 (m + hobs)) (hobs + 5)
        (fun U => mixedOldTheta M m U t ω)) := by
  classical
  have hpair := observer_parent_paired_le_two_avg_theta M hγ m t ht hobs h40 ω
  rw [show 5 + hobs = hobs + 5 from Nat.add_comm 5 hobs] at hpair
  unfold mainHotReciprocalRms_Th
  refine Real.sqrt_le_sqrt (le_trans ?_ hpair)
  refine descendantsAverage_le fun U hU => ?_
  exact le_add_of_nonneg_left (sq_nonneg _)

theorem hot_reciprocal_theta_nonneg_Th (M : ABKModel 2) (hγ : M.gamma ≤ gammaZero) (m : ℤ)
    (hobs : ℕ) (h40 : hobs ≤ 40) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (ω : Cutoff.CutoffSample 2) :
    0 ≤ descendantsAverage (originCube 2 (m + hobs)) (hobs + 5)
        (fun U => mixedOldTheta M m U t ω) := by
  classical
  have hpair := observer_parent_paired_le_two_avg_theta M hγ m t ht hobs h40 ω
  rw [show 5 + hobs = hobs + 5 from Nat.add_comm 5 hobs] at hpair
  have h0 : 0 ≤ descendantsAverage (originCube 2 (m + hobs)) (hobs + 5) (fun U =>
      oldSignedPrimalErrorSize (originCube 2 (m + hobs)) U M.nu (Annealed.sigmaBar M m : ℝ)
        M.nu_pos (Annealed.sigmaBar_characterization M m).1
        (mainELinearObsCoefficient (originCube 2 (m + hobs)) m t ω) ^ 2 +
      oldSignedReciprocalErrorSize (originCube 2 (m + hobs)) U M.nu
        (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar_characterization M m).1
        (mainELinearObsCoefficient (originCube 2 (m + hobs)) m t ω) ^ 2) := by
    unfold descendantsAverage
    exact mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun U _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
  linarith

end

end ASDExplicitGamma.Main
