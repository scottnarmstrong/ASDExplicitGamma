module

public import ASDExplicitGamma.Native.HeatVHEATDriftConfiguredCoefficients
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

/-! The `ns`-shell generalization of `HeatVHEATDriftConfiguredCoefficients`. -/

@[expose] public section


namespace ASDExplicitGamma.Native
open Inverse Variational Numerics.Native
noncomputable section

variable (ns : ℕ)

/-- The actual refined source sums consume the complete q=1 source budgets.
The exact reindexing has already been proved on the physical coefficients. -/
theorem heatVHEATDrift_source_sums_le_configured_Gen (n : ℤ) :
    (heatVHEATDriftKActualGen ns) n ≤ (nativeHeatK:ℝ) ∧
    (heatVHEATDriftCActualGen ns) ≤ (nativeHeatM:ℝ) := by
  have hid := (heatVHEATDrift_source_sums_eq_refined_row_Gen ns) n
  rw [hid.1,hid.2]
  exact (nativeHeatQ3RefinedShellCoefficientSums_le_Gen ns)

end
end ASDExplicitGamma.Native
