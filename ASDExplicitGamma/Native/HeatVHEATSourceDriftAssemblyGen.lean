module

public import ASDExplicitGamma.Native.HeatVHEATSourceDriftAssembly
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
public import ASDExplicitGamma.Native.HeatVHEATRefinedThetaRowsGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedThetaSourceRowsGen
public import ASDExplicitGamma.Native.HeatVHEATSourceAssemblyGen

/-! The `ns`-shell generalization of `HeatVHEATSourceDriftAssembly`. -/

@[expose] public section


namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Numerics.Native
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ProbabilityTheory
open scoped ENNReal NNReal

variable (ns : ℕ) [NeZero ns]

/-- The first-line refined VHEAT expectation row on the actual source carrier.
the coordinate measurability and marginal laws discharge the carrier
inputs, while the construction retains the full actual `9^10` child aggregation. -/
theorem nativeHeatQ3RefinedCarrierSourceDriftExpectationGen (hns : ns ≤ 1331)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (Ffam : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m ns)
    (hpast : ∀ l < m + 1, nativeInductionState M h l)
    (hstate : nativeInductionState M h (m + 1))
    (θ t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (k : ℕ) (hk : 1 ≤ k) (hk20 : k ≤ 20) :
    let g := nativeHeatQ3RefinedCarrierSourceAuxCenterGaussianGen M m ns Ffam θ t
    let v := nativeHeatQ3RefinedCarrierSourceAuxCenterVarianceGen M m ns Ffam θ t
    let μ := nativeHeatRemainderJointLaw M
    let A := (heatVHEATDriftRefinedAverageGen ns) M m t g
    let X := (heatVHEATDriftSourceXExtendedGen ns) Finset.univ M (m + 1) t
      (heatVHEATDriftRefinedShift m) g
    let F := heatRefinedRawEnvelope ns (heatVHEATDriftAuxVariance Finset.univ v)
    X < ⊤ ∧
      Integrable ((heatVHEATDriftRefinedSourceGen ns) M h m t k g) μ ∧
      (∫ z, (heatVHEATDriftRefinedSourceGen ns) M h m t k g z ∂μ) ≤
        (k : ℝ) * (heatVHEATDriftEGen ns) M *
          (2 * (nativeHeatK : ℝ) * (3683 / 2500 : ℝ) +
            (nativeHeatM : ℝ) * (3683 / 2500 : ℝ) ^ 2) *
          ((∫ z, A z ^ k ∂μ) + 4 * (∫ z, A z ^ (k - 1) ∂μ)) +
        heatVHEATDriftFirstLine k ((heatVHEATDriftEGen ns) M)
          nativeHeatK nativeHeatM (3683 / 2500) (3 / 10 ^ 46) X.toReal F := by
  let g := nativeHeatQ3RefinedCarrierSourceAuxCenterGaussianGen M m ns Ffam θ t
  let v := nativeHeatQ3RefinedCarrierSourceAuxCenterVarianceGen M m ns Ffam θ t
  simpa [g, v] using
    ((nativeHeat_vheat_refined_drift_expectation_Gen ns hns) M h hM hg m hpast hstate t ht
      k hk hk20 g
      (fun i => nativeHeatQ3RefinedCarrierSourceAuxCenterGaussianGen_measurable M m ns Ffam θ t i)
      v
      (fun i => nativeHeatQ3RefinedCarrierSourceAuxCenterGaussianGen_law M m ns Ffam θ t i))

end ASDExplicitGamma.Native

end
