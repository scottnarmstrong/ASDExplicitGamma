module

public import ASDExplicitGamma.Native.HeatVHEATRefinedThetaPointwise
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

/-! The `ns`-shell generalization of `HeatVHEATRefinedThetaPointwise`. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization Gaussian Algsuperdiff.Section3 Numerics.Native
open ASDExplicitGamma.Inverse ASDExplicitGamma.Response ASDExplicitGamma.Variational
open ASDExplicitGamma.Triadic ASDExplicitGamma.Main
open scoped ENNReal NNReal
noncomputable section

variable (ns : ℕ) [NeZero ns]

/-- The actual nine-shell source row, defined at the pointwise interface so
the generator and its expectation use one shared expression. -/
noncomputable def nativeHeatQ3RefinedCarrierSourceRowsForFieldsGen
    (M : ABKModel 2) (h : ℝ) (m : ℤ)
    (fields : ∀ i : nativeHeatQ3RefinedCarrierIndex,
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ)) : ℝ := by
  let σ : ℝ := Annealed.sigmaBar M (m + 1)
  exact ∑ d : Fin ns,
    4 * (q3ModelAmplitude M h (m + ((d.val + 2 : ℕ) : ℤ)) ^ 2 / σ ^ 2) *
      q3GridOverlapFactor 10 (d.val + 2) *
      (lemmaVH2Bn
        (cubeScaleFactor (originCube 2 m) /
          (q3ModelLength (m + ((d.val + 2 : ℕ) : ℤ))).1)
        (diagMeshRadius (originCube 2 m)
          (pureFluxBankSourceDepth (d.val + 2)) /
          (q3ModelLength (m + ((d.val + 2 : ℕ) : ℤ))).1)) ^ 2 *
      ((Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
        ∑ i : nativeHeatQ3RefinedCarrierIndex,
          let Qi := nativeHeatQ3RefinedCarrierChild m i
          let A := nativeHeat_translateTriadicFieldToOrigin Qi
          let ki := pureFluxOpenResponseRestriction Qi.scale
            (A (fields i))
          let Bi := lemmaVTileHistory (originCube 2 Qi.scale)
            (pureFluxBankSourceDepth (d.val + 2))
            (responseFramePlanarCoefficientField M.nu σ ki)
          let Ti := modelTraceObservable Qi.scale M.nu σ
            (A (fields i))
          Bi ^ 2 * Ti * (Ti + 4))

noncomputable def nativeHeatQ3RefinedCarrierSourceRowsGen
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (t : ℝ)
    (g : nativeHeatQ3RefinedCarrierIndex → (ℕ → ℝ) → ℝ)
    (z : Cutoff.CutoffSample 2 × (ℕ → ℝ)) : ℝ :=
  (nativeHeatQ3RefinedCarrierSourceRowsForFieldsGen ns) M h m
    (fun i => (heatVHEATDriftRefinedChildFieldGen ns) m t g z i)
