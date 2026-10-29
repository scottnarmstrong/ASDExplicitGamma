module

public import ASDExplicitGamma.Native.HeatInitialNumericsRange1Gen
public import ASDExplicitGamma.Native.HeatInitialNumericsRange2Gen
public import ASDExplicitGamma.Native.HeatInitialNumericsRange3Gen
public import ASDExplicitGamma.Native.HeatInitialNumericsRange4Gen
public import ASDExplicitGamma.Native.HeatInitialNumericsRange5Gen
public import ASDExplicitGamma.Native.HeatInitialNumericsRange6Gen
public import ASDExplicitGamma.Native.HeatInitialNumericsRange7Gen
public import ASDExplicitGamma.Native.HeatInitialNumericsRange8Gen

/-! The numeric certificates of the `ns`-shell refined initial moment for every
`9 ≤ ns ≤ 160`. -/

@[expose] public section

namespace ASDExplicitGamma.Native

/-- The numeric certificates for every `9 ≤ ns ≤ 160`. -/
theorem nativeHeatGenNum_of_range (ns : ℕ) (hns : 9 ≤ ns) (hns' : ns ≤ 160) :
    NativeHeatGenNum ns := by
  by_cases h1 : ns < 28
  · exact nativeHeatGenNum_range1_Gen ns (by omega) h1
  by_cases h2 : ns < 47
  · exact nativeHeatGenNum_range2_Gen ns (by omega) h2
  by_cases h3 : ns < 66
  · exact nativeHeatGenNum_range3_Gen ns (by omega) h3
  by_cases h4 : ns < 85
  · exact nativeHeatGenNum_range4_Gen ns (by omega) h4
  by_cases h5 : ns < 104
  · exact nativeHeatGenNum_range5_Gen ns (by omega) h5
  by_cases h6 : ns < 123
  · exact nativeHeatGenNum_range6_Gen ns (by omega) h6
  by_cases h7 : ns < 142
  · exact nativeHeatGenNum_range7_Gen ns (by omega) h7
  · exact nativeHeatGenNum_range8_Gen ns (by omega) (by omega)

end ASDExplicitGamma.Native
