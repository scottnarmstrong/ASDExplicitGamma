module
public import ASDExplicitGamma.Numerics.Native.Heat105Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat105Y00_formula : nativeHeat105Y00 = nativeHeat105Frames.y := by
  decide +kernel

theorem nativeHeat105All48 : nativeHeatPasses nativeGap106Old nativeHeat105Frames nativeHeat105Coef nativeHeat105Fixed nativeHeat105Base 48 nativeHeat105Frames.y = nativeHeat105Y48 := by
  rw [← nativeHeat105Y00_formula]
  have h4 : nativeHeatPasses nativeGap106Old nativeHeat105Frames nativeHeat105Coef nativeHeat105Fixed nativeHeat105Base 4 nativeHeat105Y00 = nativeHeat105Y04 := nativeHeat105Pass04
  have h8 : nativeHeatPasses nativeGap106Old nativeHeat105Frames nativeHeat105Coef nativeHeat105Fixed nativeHeat105Base 8 nativeHeat105Y00 = nativeHeat105Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat105Pass08]
  have h12 : nativeHeatPasses nativeGap106Old nativeHeat105Frames nativeHeat105Coef nativeHeat105Fixed nativeHeat105Base 12 nativeHeat105Y00 = nativeHeat105Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat105Pass12]
  have h16 : nativeHeatPasses nativeGap106Old nativeHeat105Frames nativeHeat105Coef nativeHeat105Fixed nativeHeat105Base 16 nativeHeat105Y00 = nativeHeat105Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat105Pass16]
  have h20 : nativeHeatPasses nativeGap106Old nativeHeat105Frames nativeHeat105Coef nativeHeat105Fixed nativeHeat105Base 20 nativeHeat105Y00 = nativeHeat105Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat105Pass20]
  have h24 : nativeHeatPasses nativeGap106Old nativeHeat105Frames nativeHeat105Coef nativeHeat105Fixed nativeHeat105Base 24 nativeHeat105Y00 = nativeHeat105Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat105Pass24]
  have h28 : nativeHeatPasses nativeGap106Old nativeHeat105Frames nativeHeat105Coef nativeHeat105Fixed nativeHeat105Base 28 nativeHeat105Y00 = nativeHeat105Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat105Pass28]
  have h32 : nativeHeatPasses nativeGap106Old nativeHeat105Frames nativeHeat105Coef nativeHeat105Fixed nativeHeat105Base 32 nativeHeat105Y00 = nativeHeat105Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat105Pass32]
  have h36 : nativeHeatPasses nativeGap106Old nativeHeat105Frames nativeHeat105Coef nativeHeat105Fixed nativeHeat105Base 36 nativeHeat105Y00 = nativeHeat105Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat105Pass36]
  have h40 : nativeHeatPasses nativeGap106Old nativeHeat105Frames nativeHeat105Coef nativeHeat105Fixed nativeHeat105Base 40 nativeHeat105Y00 = nativeHeat105Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat105Pass40]
  have h44 : nativeHeatPasses nativeGap106Old nativeHeat105Frames nativeHeat105Coef nativeHeat105Fixed nativeHeat105Base 44 nativeHeat105Y00 = nativeHeat105Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat105Pass44]
  have h48 : nativeHeatPasses nativeGap106Old nativeHeat105Frames nativeHeat105Coef nativeHeat105Fixed nativeHeat105Base 48 nativeHeat105Y00 = nativeHeat105Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat105Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
