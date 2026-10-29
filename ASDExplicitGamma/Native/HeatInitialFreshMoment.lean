module

public import ASDExplicitGamma.Native.HeatInitialMoments
public import ASDExplicitGamma.Native.HeatFiniteBandCenters
public import ASDExplicitGamma.Numerics.Native.HeatParametersData
public import ASDExplicitGamma.Numerics.Native.Heat009Initial
public import ASDExplicitGamma.Native.HeatInitialCrossRow

/-! Moment interpolation for the RMS of the fresh q3 vector. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Numerics.Native
open MeasureTheory
open scoped ENNReal

theorem nativeHeat009_qMoment_outer_root_valid (q : ℕ)
    (hq1 : 1 ≤ q) (hq10 : q ≤ 10) :
    nativeRootValid (nativeRootUp (nativeHeat009Qm.getD q 0) q) 2 = true := by
  interval_cases q <;> decide +kernel

end ASDExplicitGamma.Native
