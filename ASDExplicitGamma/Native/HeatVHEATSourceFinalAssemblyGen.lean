module

public import ASDExplicitGamma.Native.HeatVHEATSourceFinalAssembly
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

/-! The `ns`-shell generalization of `HeatVHEATSourceFinalAssembly`. -/

@[expose] public section


namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization ASDExplicitGamma.Gaussian
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Numerics.Native
open scoped ENNReal Topology

variable (ns : ℕ) [NeZero ns]

/-- The actual source-(8) average cap: the L20 seminorm of the heat-augmented
average of all refined child traces on the common source probability space. -/
noncomputable def nativeHeatQ3RefinedCarrierSourceAverageNormGen
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ)
    (Ffam : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m ns) (θ t : ℝ) : ℝ :=
  (eLpNorm
    ((heatVHEATDriftRefinedAverageGen ns) M m t
      (nativeHeatQ3RefinedCarrierSourceAuxCenterGaussianGen M m ns Ffam θ t))
    20 (nativeHeatRemainderJointLaw M)).toReal

/-- Once the proof supplies the source-normalized expectation row for separate
individual, average, and raw-envelope caps `X`, `Y`, and `F`, the actual
source-carrier moment has the differential-only VHEAT output at the configured
heat parameter. The time-zero cap remains in NA-REFINED-HEAT. -/
theorem nativeHeatQ3RefinedCarrierSourceVHEATBackwardInequality_of_expectationRowGen
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ)
    (Ffam : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m ns) (X Y F : ℝ)
    (hcaps : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 →
      ((heatVHEATDriftRefinedPhysicalXExtendedGen ns) M m t
        (nativeHeatQ3RefinedCarrierSourceAuxCenterGaussianGen M m ns Ffam
          (nativeHeatTheta : ℝ) t)).toReal ≤ X ∧
      (nativeHeatQ3RefinedCarrierSourceAverageNormGen ns) M h hM m Ffam
          (nativeHeatTheta : ℝ) t ≤ Y ∧
      heatRefinedRawEnvelope ns
        (heatVHEATDriftAuxVariance Finset.univ
          (nativeHeatQ3RefinedCarrierSourceAuxCenterVarianceGen M m ns Ffam
            (nativeHeatTheta : ℝ) t)) ≤ F)
    (hlocal : ∀ k : ℕ, 1 ≤ k → k ≤ 20 → ∀ t : ℝ,
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
          X Y (3 / 10 ^ 46 : ℝ) F) :
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
          X Y (3 / 10 ^ 46 : ℝ) F := by
  have hθ : 0 < (nativeHeatTheta : ℝ) := by norm_num [nativeHeatTheta]
  intro k hk₁ hk₂ t ht
  have hderiv := (nativeHeatQ3RefinedCarrierSourceMoment_hasDerivAt_Gen ns)
    M h hM m Ffam (nativeHeatTheta : ℝ) hθ k (Nat.ne_of_gt (by omega)) ht
  refine ⟨hderiv, ?_⟩
  rw [hderiv.deriv]
  rcases hcaps t ht with ⟨hX, hY, hF⟩
  exact hlocal k hk₁ hk₂ t ht hX hY hF

end ASDExplicitGamma.Native

end
