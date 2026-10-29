module

public import ASDExplicitGamma.Native.HeatVHEATRefinedAssembly
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

/-! The `ns`-shell generalization of `HeatVHEATRefinedAssembly`. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Set Homogenization
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Numerics.Native
open scoped ENNReal Topology

variable (ns : ℕ) [NeZero ns]

/-- The complete physical shell band of the refined depth-ten carrier has
its selected direct-sum Gaussian-series law. -/
theorem nativeHeatQ3RefinedCarrierBandLawGen
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ)
    (Ffam : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m ns) :
    (Cutoff.cutoffSampleLaw M).toMeasure.map
        (modelBand (nativeHeatQ3RefinedCarrierDomain m)
          (nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns)) =
      standardGaussianInfinitePi.map
        (gaussianSeriesLimitE
          (nativeHeatQ3RefinedCarrierFreshShellSeriesSummableGen Ffam)
          (nativeHeatQ3RefinedCarrierFreshShellSeriesFactorGen Ffam)) :=
  nativeHeatQ3RefinedCarrierFreshShellSeriesLawGen Ffam

theorem nativeHeatQ3RefinedCarrierBands_afterOldLabel_Gen (m : ℤ) (d : Fin ns) :
    m + 1 < nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns d := by
  simp only [nativeHeatQ3RefinedCarrierPhysicalShellsGen]
  omega
