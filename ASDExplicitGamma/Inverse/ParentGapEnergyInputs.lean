module

public import ASDExplicitGamma.Inverse.RawParentGapInputs
public import ASDExplicitGamma.Inverse.SourceInterfaceEnergy
public import ASDExplicitGamma.Inverse.BridgeObservables

/-! Exact source inputs assembled for the OLD parent-gap consumer. -/

@[expose] public section

namespace ASDExplicitGamma.Inverse

open MeasureTheory Homogenization Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Triadic
open scoped ENNReal

/-- Exact termwise identification of the bridge's OLD chronology with the
complete source-energy slope series. -/
theorem mixed_bridge_xi_slope_eq_source_series
    (M : ABKModel 2) (h : ℝ) (m : ℤ) :
    mixedBridgeXiSlope M h m =
      ∑' j : ℕ, inSourceOldEnergyHistoryWeight M j *
        inSourceMeanSlopeActual M h m j := by
  unfold mixedBridgeXiSlope
  apply tsum_congr
  intro j
  unfold mixedBridgeOldInverseBaseline inSourceOldEnergyHistoryWeight
  ring

/-! The exact finite OLD-energy conclusion as a consumer input, with the
raw transport, rare-sum, and weak-history producers instantiated separately. -/

end ASDExplicitGamma.Inverse
