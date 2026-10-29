module
public import ASDExplicitGamma.Numerics.Native.Heat050Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat050Y00_formula : nativeHeat050Y00 = nativeHeat050Frames.y := by
  decide +kernel

theorem nativeHeat050All48 : nativeHeatPasses nativeGap051Old nativeHeat050Frames nativeHeat050Coef nativeHeat050Fixed nativeHeat050Base 48 nativeHeat050Frames.y = nativeHeat050Y48 := by
  rw [← nativeHeat050Y00_formula]
  have h4 : nativeHeatPasses nativeGap051Old nativeHeat050Frames nativeHeat050Coef nativeHeat050Fixed nativeHeat050Base 4 nativeHeat050Y00 = nativeHeat050Y04 := nativeHeat050Pass04
  have h8 : nativeHeatPasses nativeGap051Old nativeHeat050Frames nativeHeat050Coef nativeHeat050Fixed nativeHeat050Base 8 nativeHeat050Y00 = nativeHeat050Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat050Pass08]
  have h12 : nativeHeatPasses nativeGap051Old nativeHeat050Frames nativeHeat050Coef nativeHeat050Fixed nativeHeat050Base 12 nativeHeat050Y00 = nativeHeat050Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat050Pass12]
  have h16 : nativeHeatPasses nativeGap051Old nativeHeat050Frames nativeHeat050Coef nativeHeat050Fixed nativeHeat050Base 16 nativeHeat050Y00 = nativeHeat050Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat050Pass16]
  have h20 : nativeHeatPasses nativeGap051Old nativeHeat050Frames nativeHeat050Coef nativeHeat050Fixed nativeHeat050Base 20 nativeHeat050Y00 = nativeHeat050Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat050Pass20]
  have h24 : nativeHeatPasses nativeGap051Old nativeHeat050Frames nativeHeat050Coef nativeHeat050Fixed nativeHeat050Base 24 nativeHeat050Y00 = nativeHeat050Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat050Pass24]
  have h28 : nativeHeatPasses nativeGap051Old nativeHeat050Frames nativeHeat050Coef nativeHeat050Fixed nativeHeat050Base 28 nativeHeat050Y00 = nativeHeat050Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat050Pass28]
  have h32 : nativeHeatPasses nativeGap051Old nativeHeat050Frames nativeHeat050Coef nativeHeat050Fixed nativeHeat050Base 32 nativeHeat050Y00 = nativeHeat050Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat050Pass32]
  have h36 : nativeHeatPasses nativeGap051Old nativeHeat050Frames nativeHeat050Coef nativeHeat050Fixed nativeHeat050Base 36 nativeHeat050Y00 = nativeHeat050Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat050Pass36]
  have h40 : nativeHeatPasses nativeGap051Old nativeHeat050Frames nativeHeat050Coef nativeHeat050Fixed nativeHeat050Base 40 nativeHeat050Y00 = nativeHeat050Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat050Pass40]
  have h44 : nativeHeatPasses nativeGap051Old nativeHeat050Frames nativeHeat050Coef nativeHeat050Fixed nativeHeat050Base 44 nativeHeat050Y00 = nativeHeat050Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat050Pass44]
  have h48 : nativeHeatPasses nativeGap051Old nativeHeat050Frames nativeHeat050Coef nativeHeat050Fixed nativeHeat050Base 48 nativeHeat050Y00 = nativeHeat050Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat050Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
