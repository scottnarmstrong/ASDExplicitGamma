module

public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedPhysical
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

/-! The `ns`-shell generalization of `HeatVHEATDriftRefinedPhysical`. -/

@[expose] public section


namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Algsuperdiff.Section3
noncomputable section

variable (ns : ℕ)

local instance heatVHEATDriftRefinedPhysicalChildFiniteGenDriftRefinedPhysical (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    IsFiniteMeasure (volumeMeasureOn (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) :=
  ((isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isBoundedDomain).isFiniteMeasure_restrict_volume

/-- The actual physical OLD-plus-fresh-band field on a refined child, with
its auxiliary scalar added only to that child's test. -/
def heatVHEATDriftRefinedChildFieldGen (m : ℤ) (t : ℝ)
    (g : nativeHeatQ3RefinedCarrierIndex → (ℕ → ℝ) → ℝ)
    (z : Cutoff.CutoffSample 2 × (ℕ → ℝ)) (i : nativeHeatQ3RefinedCarrierIndex) :
    C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)),ℝ) :=
  nativeHeatQ3RefinedCarrierOldMap m
    (olderField (nativeHeatQ3RefinedCarrierDomain m) (m+1) z.1+
      Real.sqrt t • modelBand (nativeHeatQ3RefinedCarrierDomain m)
        (nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns) z.1) i+
    ContinuousMap.const _ (g i z.2)

/-- Actual common-frame physical child trace on the same two noises. -/
def heatVHEATDriftRefinedPhysicalTraceGen (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (g : nativeHeatQ3RefinedCarrierIndex → (ℕ → ℝ) → ℝ)
    (z : Cutoff.CutoffSample 2 × (ℕ → ℝ)) (i : nativeHeatQ3RefinedCarrierIndex) : ℝ :=
  childTraceObservable (measurableSet_cubeSet (nativeHeatQ3RefinedCarrierChild m i))
    (volume_cubeSet_toReal_pos (nativeHeatQ3RefinedCarrierChild m i)) M.nu
    (Annealed.sigmaBar M (m+1)) M.nu_pos (Annealed.sigmaBar_characterization M (m+1)).1
    ((heatVHEATDriftRefinedChildFieldGen ns) m t g z i)

/-- The actual physical trace average on the depth-ten carrier. -/
def heatVHEATDriftRefinedPhysicalAverageGen (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (g : nativeHeatQ3RefinedCarrierIndex → (ℕ → ℝ) → ℝ)
    (z : Cutoff.CutoffSample 2 × (ℕ → ℝ)) : ℝ :=
  ∑ i : nativeHeatQ3RefinedCarrierIndex,
    heatVHEATDriftRefinedWeight*(heatVHEATDriftRefinedPhysicalTraceGen ns) M m t g z i

/-- Literal sum of the owner's centered signed drift/mixed profiles on the
actual sheared physical child fields, with the actual polynomial power weight. -/
def heatVHEATDriftRefinedPhysicalDriftGen (M : ABKModel 2) (h : ℝ) (m : ℤ) (t : ℝ) (k : ℕ)
    (g : nativeHeatQ3RefinedCarrierIndex → (ℕ → ℝ) → ℝ)
    (z : Cutoff.CutoffSample 2 × (ℕ → ℝ)) : ℝ :=
  ∑ i : nativeHeatQ3RefinedCarrierIndex,heatVHEATDriftRefinedWeight*
    ((k:ℝ)*((heatVHEATDriftRefinedPhysicalAverageGen ns) M m t g z)^(k-1)*
      ∑ d : Fin ns,(nativeHeatQ3RefinedCarrierChildSignedOffDiagonalProfileGen ns) M h m i d
        (Annealed.sigmaBar M (m+1)) ((heatVHEATDriftRefinedChildFieldGen ns) m t g z i))

end
end ASDExplicitGamma.Native
