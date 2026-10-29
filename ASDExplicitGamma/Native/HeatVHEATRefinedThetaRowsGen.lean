module

public import ASDExplicitGamma.Native.HeatVHEATRefinedThetaRows
public import ASDExplicitGamma.Native.HeatVHEATSourceCarrierGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedShellLawGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceClocksGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedSourceProfilesGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedSourceTransportGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceGeometryGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceBankGen
public import ASDExplicitGamma.Native.HeatVHEATDriftBankIdentityGen
public import ASDExplicitGamma.Native.HeatVHEATDriftBankMeasurableGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceIntegrandGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceNormsGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceExpectationGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedCoefficientsGen
public import ASDExplicitGamma.Native.HeatVHEATDriftConfiguredCoefficientsGen
public import ASDExplicitGamma.Native.HeatVHEATDriftConfiguredExpectationGen
public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedProfileGen
public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedExpectationGen
public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedPhysicalGen
public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedBindingGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedSourceObserverGen
public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedActualGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedAssemblyGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedRowGen
public import ASDExplicitGamma.Native.Q3GridOverlapGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedSupportGeometryGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedGeometryGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedObservationGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedParentLawGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedSourceMapGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedMeanVarianceGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedRemainderGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedMeanChildBoundGen
public import ASDExplicitGamma.Native.HeatVHEATBracketMeanRieszSupportGen
public import ASDExplicitGamma.Native.HeatVHEATBracketParentRieszGen
public import ASDExplicitGamma.Native.HeatVHEATBracketMeanDerivativeGen
public import ASDExplicitGamma.Native.HeatVHEATBracketMeanDerivativeCLMGen
public import ASDExplicitGamma.Native.HeatVHEATBracketMeanRieszIdentityGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedMeanRieszIdentityGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedMeanAverageProfilesGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedMeanBracketGen
public import ASDExplicitGamma.Native.HeatVHEATBracketSourceCarrierGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedDriftAssemblyGen
public import ASDExplicitGamma.Native.HeatVHEATSourceBracketGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedFinalAssemblyGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedThetaPointwiseGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedThetaProfileGen

/-! The `ns`-shell generalization of `HeatVHEATRefinedThetaRows`. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization Gaussian Inverse Response Variational Triadic
open MeasureTheory
open Algsuperdiff.Section3
open scoped ENNReal NNReal
noncomputable section

variable (ns : ℕ) [NeZero ns]

private theorem nativeHeatQ3RefinedCarrierBankLeft_le_Gen
    (M : ABKModel 2) (n : ℤ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) (g : ℝ) (d : Fin ns) :
    lemmaVTileHistory (originCube 2 (n - 1))
      (pureFluxBankSourceDepth (d.val + 2))
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n)
        (pureFluxOpenResponseRestriction (n - 1)
          (heatRefinedObserverShear (n - 1) n ns t ω g))) ≤
      (heatVHEATDriftBankGen ns) M n ns t ω g d := by
  unfold heatVHEATDriftBankGen
  exact le_max_left _ _

/-- Each actual source-row history is the left branch of the complete
physical bank, after the exact source-observer transport. -/
theorem nativeHeatQ3RefinedCarrierRowHistory_le_bank_Gen
    (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (g : nativeHeatQ3RefinedCarrierIndex → (ℕ → ℝ) → ℝ)
    (z : Cutoff.CutoffSample 2 × (ℕ → ℝ))
    (i : nativeHeatQ3RefinedCarrierIndex) (d : Fin ns) :
    let Q := nativeHeatQ3RefinedCarrierChild m i
    let A := nativeHeat_translateTriadicFieldToOrigin Q
    let x := (heatVHEATDriftRefinedChildFieldGen ns) m t g z i
    lemmaVTileHistory (originCube 2 Q.scale)
      (pureFluxBankSourceDepth (d.val + 2))
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M (m + 1))
        (pureFluxOpenResponseRestriction Q.scale (A x))) ≤
      (heatVHEATDriftBankGen ns) M (m + 1) ns t
        (Cutoff.translateCutoffSample (heatVHEATDriftRefinedShift m i) z.1)
        (g i z.2) d := by
  let Q := nativeHeatQ3RefinedCarrierChild m i
  let A := nativeHeat_translateTriadicFieldToOrigin Q
  let x := (heatVHEATDriftRefinedChildFieldGen ns) m t g z i
  have hobs : A x = heatRefinedObserverShear Q.scale (m + 1) ns t
      (Cutoff.translateCutoffSample (heatVHEATDriftRefinedShift m i) z.1)
      (g i z.2) := by
    have hh := (heatVHEATDrift_refined_child_observer_Gen ns) M m t g z i
    simpa [A, x, Q] using hh
  have hbank := (nativeHeatQ3RefinedCarrierBankLeft_le_Gen ns) M (m + 1) t
    (Cutoff.translateCutoffSample (heatVHEATDriftRefinedShift m i) z.1)
    (g i z.2) d
  have hrow :
      lemmaVTileHistory (originCube 2 Q.scale)
        (pureFluxBankSourceDepth (d.val + 2))
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M (m + 1))
          (pureFluxOpenResponseRestriction Q.scale (A x))) =
      lemmaVTileHistory (originCube 2 ((m + 1) - 1))
        (pureFluxBankSourceDepth (d.val + 2))
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M (m + 1))
          (pureFluxOpenResponseRestriction ((m + 1) - 1)
            (heatRefinedObserverShear ((m + 1) - 1) (m + 1) ns t
              (Cutoff.translateCutoffSample (heatVHEATDriftRefinedShift m i) z.1)
              (g i z.2)))) := by
    have hscale : Q.scale = m := nativeHeatQ3RefinedCarrierChild_scale m i
    let H : ℤ → ℝ := fun r =>
      lemmaVTileHistory (originCube 2 r) (pureFluxBankSourceDepth (d.val + 2))
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M (m + 1))
          (pureFluxOpenResponseRestriction r
            (heatRefinedObserverShear r (m + 1) ns t
              (Cutoff.translateCutoffSample (heatVHEATDriftRefinedShift m i) z.1)
              (g i z.2))))
    have hscale' : Q.scale = (m + 1) - 1 := by omega
    rw [hobs]
    change H Q.scale = H ((m + 1) - 1)
    exact congrArg H hscale'
  dsimp only
  rw [hrow]
  exact hbank

end
end ASDExplicitGamma.Native
