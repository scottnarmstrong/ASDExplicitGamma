module

public import ASDExplicitGamma.Native.HeatVHEATBracketMeanDerivativeCLM
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

/-! The `ns`-shell generalization of `HeatVHEATBracketMeanDerivativeCLM`. -/

@[expose] public section


namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Main ASDExplicitGamma.Triadic
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3

noncomputable section

variable (ns : ℕ) [NeZero ns]

/-- The pointwise parent-source identity, assembled as an equality of
continuous linear functionals on white noise. -/
theorem nativeHeatQ3RefinedCarrierParentMeanDerivativeCLM_eq_remainderObservations_Gen
    (M : ABKModel 2) (h : ℝ)
    (m : ℤ) (d : Fin ns) (σ : ℝ) (hσ : 0 < σ)
    (x : ∀ i : nativeHeatQ3RefinedCarrierIndex,
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ)) :
    (((fderiv ℝ (nativeHeatQ3RefinedCarrierMeanTrace M m σ hσ) x).comp
      (nativeHeatQ3RefinedCarrierRemainderMap m)).comp
      (nativeHeatQ3RefinedCarrierParentRestrict m)).comp
      ((nativeHeatQ3RefinedCarrierParentSourceGen' ns) M h m d) =
      (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ •
        ∑ i : nativeHeatQ3RefinedCarrierIndex,
          (nativeHeatQ3RefinedCarrierChildRemainderMeanObservationGen ns)
            M h m d σ x i := by
  classical
  let L : WhiteNoise →L[ℝ] ℝ :=
    (((fderiv ℝ (nativeHeatQ3RefinedCarrierMeanTrace M m σ hσ) x).comp
      (nativeHeatQ3RefinedCarrierRemainderMap m)).comp
      (nativeHeatQ3RefinedCarrierParentRestrict m)).comp
      ((nativeHeatQ3RefinedCarrierParentSourceGen' ns) M h m d)
  have hpoint (u : WhiteNoise) : L u =
      (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
        ∑ i : nativeHeatQ3RefinedCarrierIndex,
        (nativeHeatQ3RefinedCarrierChildRemainderMeanObservationGen ns)
          M h m d σ x i u := by
    change fderiv ℝ (nativeHeatQ3RefinedCarrierMeanTrace M m σ hσ) x
        (nativeHeatQ3RefinedCarrierRemainderMap m
          (nativeHeatQ3RefinedCarrierParentRestrict m
            ((nativeHeatQ3RefinedCarrierParentSourceGen' ns) M h m d u))) =
      (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
        ∑ i : nativeHeatQ3RefinedCarrierIndex,
          (nativeHeatQ3RefinedCarrierChildRemainderMeanObservationGen ns)
            M h m d σ x i u
    exact (nativeHeatQ3RefinedCarrierParentMeanDerivative_eq_remainderObservations_Gen ns)
      M h m d σ hσ x u
  have hsum : L =
      (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ •
        ∑ i : nativeHeatQ3RefinedCarrierIndex,
          (nativeHeatQ3RefinedCarrierChildRemainderMeanObservationGen ns)
            M h m d σ x i := by
    ext u
    simp only [smul_apply, sum_apply, smul_eq_mul]
    exact hpoint u
  calc
    _ = L := rfl
    _ = _ := hsum
    _ = _ := rfl

end

end ASDExplicitGamma.Native
