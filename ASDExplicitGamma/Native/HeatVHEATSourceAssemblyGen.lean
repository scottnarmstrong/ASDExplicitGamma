module

public import ASDExplicitGamma.Native.HeatVHEATSourceAssembly
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

/-! The `ns`-shell generalization of `HeatVHEATSourceAssembly`. -/

@[expose] public section


namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Numerics.Native
open scoped ENNReal Topology

variable (ns : ℕ) [NeZero ns]

local instance nativeHeatQ3RefinedSourceAssemblyChildFiniteGenSourceAssembly (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    IsFiniteMeasure
      (volumeMeasureOn (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) :=
  ((isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isBoundedDomain).isFiniteMeasure_restrict_volume

/-- The source-normalized actual complete-band moment has its exact
cancelled-generator derivative on the open heat interval. -/
theorem nativeHeatQ3RefinedCarrierSourceMoment_hasDerivAt_Gen
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ)
    (Ffam : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m ns) (θ : ℝ) (hθ : 0 < θ)
    (k : ℕ) (hk : k ≠ 0) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun s => nativeHeatQ3RefinedCarrierSourceMomentGen M m ns Ffam k θ s)
      (nativeHeatQ3RefinedCarrierSourceMomentGeneratorGen M m ns Ffam k θ t) t := by
  let U : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) :=
    fun i => cubeSet (nativeHeatQ3RefinedCarrierChild m i)
  let hU : ∀ i : nativeHeatQ3RefinedCarrierIndex, MeasurableSet (U i) :=
    fun i => measurableSet_cubeSet (nativeHeatQ3RefinedCarrierChild m i)
  let hvol : ∀ i : nativeHeatQ3RefinedCarrierIndex,
      0 < (volume (U i)).toReal :=
    fun i => volume_cubeSet_toReal_pos (nativeHeatQ3RefinedCarrierChild m i)
  let bands := nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns
  let P := nativeHeatQ3RefinedCarrierOldMap m
  let L := nativeHeatQ3RefinedCarrierSourceCenterMap m
  let hA := nativeHeatQ3RefinedCarrierFreshShellSeriesSummableGen Ffam
  let T := nativeHeatQ3RefinedCarrierFreshShellSeriesFactorGen Ffam
  have hbands : ∀ d : Fin ns, m + 1 < bands d := by
    intro d
    exact (nativeHeatQ3RefinedCarrierBands_afterOldLabel_Gen ns) m d
  have hlaw := (nativeHeatQ3RefinedCarrierBandLawGen ns) M h hM m Ffam
  simpa [nativeHeatQ3RefinedCarrierSourceMomentGen,
    nativeHeatQ3RefinedCarrierSourceMomentGeneratorGen,
    U, hU, hvol, bands, P, L, hA, T] using
    (nativeHeatChildBandMoment_hasDerivAt U hU hvol
      M.nu (Annealed.sigmaBar M (m + 1) : ℝ) M.nu_pos
      (Annealed.sigmaBar_characterization M (m + 1)).1
      (nativeHeatQ3RefinedCarrierDomain m) M (m + 1) bands hbands P L hA T θ hθ hlaw
      k hk ht)

end ASDExplicitGamma.Native

end
