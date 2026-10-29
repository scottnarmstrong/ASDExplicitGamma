module

public import ASDExplicitGamma.Native.HeatVHEATSourceNode
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
public import ASDExplicitGamma.Native.HeatVHEATSourceDriftAssemblyGen
public import ASDExplicitGamma.Native.HeatVHEATSourceFinalAssemblyGen
public import ASDExplicitGamma.Native.HeatVHEATSourcePointwiseGen
public import ASDExplicitGamma.Native.HeatVHEATSourceExpectationGen

/-! The `ns`-shell generalization of `HeatVHEATSourceNode`. -/

@[expose] public section


namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization ASDExplicitGamma.Gaussian
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Numerics.Native

variable (ns : ℕ) [NeZero ns]

/-- The source-coefficient-4 expectation row on the source carrier. -/
theorem nativeHeatQ3RefinedCarrierSourceExpectationRow_Gen (hns : ns ≤ 1331)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (Ffam : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m ns)
    (hpast : ∀ l < m + 1, nativeInductionState M h l)
    (hstate : nativeInductionState M h (m + 1))
    (X Y F : ℝ) :
    ∀ k : ℕ, 1 ≤ k → k ≤ 20 → ∀ t : ℝ,
      (ht : t ∈ Set.Ioo (0 : ℝ) 1) →
      (((heatVHEATDriftRefinedPhysicalXExtendedGen ns) M m t
        (nativeHeatQ3RefinedCarrierSourceAuxCenterGaussianGen M m ns Ffam
          (nativeHeatTheta : ℝ) t)).toReal ≤ X) →
      ((nativeHeatQ3RefinedCarrierSourceAverageNormGen ns) M h hM m Ffam
        (nativeHeatTheta : ℝ) t ≤ Y) →
      (heatRefinedRawEnvelope ns
        (heatVHEATDriftAuxVariance Finset.univ
          (nativeHeatQ3RefinedCarrierSourceAuxCenterVarianceGen M m ns Ffam
            (nativeHeatTheta : ℝ) t)) ≤ F) →
      nativeHeatQ3RefinedCarrierSourceMomentGeneratorGen M m ns Ffam k
          (nativeHeatTheta : ℝ) t ≤
        (k : ℝ) * (heatVHEATDriftEGen ns) M *
          (2 * (nativeHeatK : ℝ) * (3683 / 2500 : ℝ) +
            (nativeHeatM : ℝ) * (3683 / 2500 : ℝ) ^ 2) *
          (nativeHeatQ3RefinedCarrierSourceMomentGen M m ns Ffam k
              (nativeHeatTheta : ℝ) t +
            4 * nativeHeatQ3RefinedCarrierSourceMomentGen M m ns Ffam (k - 1)
              (nativeHeatTheta : ℝ) t) +
        nativeHeatVHEATErrorEk k 20 ((heatVHEATDriftEGen ns) M)
          (nativeHeatK : ℝ) (nativeHeatM : ℝ) (nativeHeatSB : ℝ)
          (nativeHeatTheta : ℝ) (3683 / 2500 : ℝ)
          X Y (3 / 10 ^ 46 : ℝ) F :=
  fun k hk hk20 t ht hX hY hF =>
    (nativeHeatQ3RefinedCarrierGeneratorBound_Gen ns hns) M h hM hg m Ffam hpast hstate
      k hk hk20 t ht X Y F hX hY hF

/-- NA-VHEAT-BACKWARD-INEQUALITY on the source carrier. -/
theorem nativeHeatVHEATBackwardInequality_source_Gen (hns : ns ≤ 1331)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (Ffam : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m ns)
    (hpast : ∀ l < m + 1, nativeInductionState M h l)
    (hstate : nativeInductionState M h (m + 1))
    (X Y F : ℝ)
    (hcaps : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 →
      ((heatVHEATDriftRefinedPhysicalXExtendedGen ns) M m t
        (nativeHeatQ3RefinedCarrierSourceAuxCenterGaussianGen M m ns Ffam
          (nativeHeatTheta : ℝ) t)).toReal ≤ X ∧
      (nativeHeatQ3RefinedCarrierSourceAverageNormGen ns) M h hM m Ffam
          (nativeHeatTheta : ℝ) t ≤ Y ∧
      heatRefinedRawEnvelope ns
        (heatVHEATDriftAuxVariance Finset.univ
          (nativeHeatQ3RefinedCarrierSourceAuxCenterVarianceGen M m ns Ffam
            (nativeHeatTheta : ℝ) t)) ≤ F) :
    ∀ k : ℕ, 1 ≤ k → k ≤ 20 → ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 →
      HasDerivAt
        (fun s => nativeHeatQ3RefinedCarrierSourceMomentGen M m ns Ffam k
          (nativeHeatTheta : ℝ) s)
        (nativeHeatQ3RefinedCarrierSourceMomentGeneratorGen M m ns Ffam k
          (nativeHeatTheta : ℝ) t) t ∧
      deriv (fun s => nativeHeatQ3RefinedCarrierSourceMomentGen M m ns Ffam k
          (nativeHeatTheta : ℝ) s) t ≤
        (k : ℝ) * (heatVHEATDriftEGen ns) M *
          (2 * (nativeHeatK : ℝ) * (3683 / 2500 : ℝ) +
            (nativeHeatM : ℝ) * (3683 / 2500 : ℝ) ^ 2) *
          (nativeHeatQ3RefinedCarrierSourceMomentGen M m ns Ffam k
              (nativeHeatTheta : ℝ) t +
            4 * nativeHeatQ3RefinedCarrierSourceMomentGen M m ns Ffam (k - 1)
              (nativeHeatTheta : ℝ) t) +
        nativeHeatVHEATErrorEk k 20 ((heatVHEATDriftEGen ns) M)
          (nativeHeatK : ℝ) (nativeHeatM : ℝ) (nativeHeatSB : ℝ)
          (nativeHeatTheta : ℝ) (3683 / 2500 : ℝ)
          X Y (3 / 10 ^ 46 : ℝ) F :=
  (nativeHeatQ3RefinedCarrierSourceVHEATBackwardInequality_of_expectationRowGen ns)
    M h hM m Ffam X Y F hcaps
    ((nativeHeatQ3RefinedCarrierSourceExpectationRow_Gen ns hns) M h hM hg m Ffam hpast hstate X Y F)

end ASDExplicitGamma.Native
