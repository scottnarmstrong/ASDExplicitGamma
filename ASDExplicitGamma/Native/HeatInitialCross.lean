module

public import ASDExplicitGamma.Native.HeatShearMoment
public import ASDExplicitGamma.Numerics.Native.HeatParametersData

/-! The state-driven child shear moments fit the cross scale in the exact
native initial heat vector. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse
open ASDExplicitGamma.Numerics.Native
open ASDExplicitGamma.Variational
open scoped ENNReal

private theorem nativeHeat_initialCrossParameters :
    (3 / 50 : ℚ) ≤ nativeQstar ∧
    (7 / 2 : ℚ) * nativeQstar ≤ nativeHeatParametersData.hp ∧
    inverseBankCap .localInverse ≤ nativeHeatB ∧
    inverseBankReserve .localInverse ≤ nativeHeatEps ∧
    (21 / 100 : ℚ) ≤ nativeHeatParametersData.hp := by
  constructor
  · norm_num [nativeQstar]
  constructor
  · norm_num [nativeHeatParametersData, nativeQstar]
  constructor
  · norm_num [inverseBankCap, nativeHeatB, nativeHeatRQ, nativeE, nativeGamma, nativeB]
  constructor
  · norm_num [inverseBankReserve, nativeHeatEps, nativeHeatRQ, nativeE, nativeGamma,
      nativeEps]
  · norm_num [nativeHeatParametersData]

/-- The configured baseline dominates the local inverse-bank cap. -/
theorem nativeHeat_localInverseCap_le_nativeHeatB :
    inverseBankCap .localInverse ≤ nativeHeatB :=
  nativeHeat_initialCrossParameters.2.2.1

end ASDExplicitGamma.Native
