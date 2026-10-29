module
public import ASDExplicitGamma.Numerics.Native.Heat036Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat036Y00_formula : nativeHeat036Y00 = nativeHeat036Frames.y := by
  decide +kernel

theorem nativeHeat036All48 : nativeHeatPasses nativeGap037Old nativeHeat036Frames nativeHeat036Coef nativeHeat036Fixed nativeHeat036Base 48 nativeHeat036Frames.y = nativeHeat036Y48 := by
  rw [← nativeHeat036Y00_formula]
  have h4 : nativeHeatPasses nativeGap037Old nativeHeat036Frames nativeHeat036Coef nativeHeat036Fixed nativeHeat036Base 4 nativeHeat036Y00 = nativeHeat036Y04 := nativeHeat036Pass04
  have h8 : nativeHeatPasses nativeGap037Old nativeHeat036Frames nativeHeat036Coef nativeHeat036Fixed nativeHeat036Base 8 nativeHeat036Y00 = nativeHeat036Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat036Pass08]
  have h12 : nativeHeatPasses nativeGap037Old nativeHeat036Frames nativeHeat036Coef nativeHeat036Fixed nativeHeat036Base 12 nativeHeat036Y00 = nativeHeat036Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat036Pass12]
  have h16 : nativeHeatPasses nativeGap037Old nativeHeat036Frames nativeHeat036Coef nativeHeat036Fixed nativeHeat036Base 16 nativeHeat036Y00 = nativeHeat036Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat036Pass16]
  have h20 : nativeHeatPasses nativeGap037Old nativeHeat036Frames nativeHeat036Coef nativeHeat036Fixed nativeHeat036Base 20 nativeHeat036Y00 = nativeHeat036Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat036Pass20]
  have h24 : nativeHeatPasses nativeGap037Old nativeHeat036Frames nativeHeat036Coef nativeHeat036Fixed nativeHeat036Base 24 nativeHeat036Y00 = nativeHeat036Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat036Pass24]
  have h28 : nativeHeatPasses nativeGap037Old nativeHeat036Frames nativeHeat036Coef nativeHeat036Fixed nativeHeat036Base 28 nativeHeat036Y00 = nativeHeat036Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat036Pass28]
  have h32 : nativeHeatPasses nativeGap037Old nativeHeat036Frames nativeHeat036Coef nativeHeat036Fixed nativeHeat036Base 32 nativeHeat036Y00 = nativeHeat036Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat036Pass32]
  have h36 : nativeHeatPasses nativeGap037Old nativeHeat036Frames nativeHeat036Coef nativeHeat036Fixed nativeHeat036Base 36 nativeHeat036Y00 = nativeHeat036Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat036Pass36]
  have h40 : nativeHeatPasses nativeGap037Old nativeHeat036Frames nativeHeat036Coef nativeHeat036Fixed nativeHeat036Base 40 nativeHeat036Y00 = nativeHeat036Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat036Pass40]
  have h44 : nativeHeatPasses nativeGap037Old nativeHeat036Frames nativeHeat036Coef nativeHeat036Fixed nativeHeat036Base 44 nativeHeat036Y00 = nativeHeat036Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat036Pass44]
  have h48 : nativeHeatPasses nativeGap037Old nativeHeat036Frames nativeHeat036Coef nativeHeat036Fixed nativeHeat036Base 48 nativeHeat036Y00 = nativeHeat036Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat036Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
