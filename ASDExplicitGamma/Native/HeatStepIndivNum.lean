module

public import ASDExplicitGamma.Native.HeatStepDefs
public import ASDExplicitGamma.Numerics.Native.Systems

/-! Numerical certificates binding the gap `ns + 1` configured individual cooperative system
(configured index `ns - 8`) to the uniform old row and individual cap of the heat step. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native

/-- The configured index of the gap `ns + 1` individual system, for `9 ≤ ns ≤ 160`. -/
def nativeHeatIndexGen (ns : ℕ) (hns : ns ≤ 160) : Fin 153 := ⟨ns - 8, by omega⟩

structure NativeHeatStepIndivNum (ns : ℕ) (hns : ns ≤ 160) : Prop where
  gap : (nativeConfiguredSystem (nativeHeatIndexGen ns hns)).gap = ns + 1
  old_source : nativeOld (ns + 1) = nativeHeatOldRowGen ns
  indiv : nativeHeatIndividualGen ns =
    (nativeUp (nativeRootUp ((nativeConfiguredSystem (nativeHeatIndexGen ns hns)).result.getD 20 0) 20 *
        (nativeConfiguredSystem (nativeHeatIndexGen ns hns)).system.z * nativeA),
     nativeUp ((nativeConfiguredSystem (nativeHeatIndexGen ns hns)).result.getD 1 0 *
        (nativeConfiguredSystem (nativeHeatIndexGen ns hns)).system.z * nativeA))
  result20_root : nativeRootValid
    ((nativeConfiguredSystem (nativeHeatIndexGen ns hns)).result.getD 20 0) 20 = true

end ASDExplicitGamma.Native

end
