module
public import ASDExplicitGamma.Numerics.Native.Heat078Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat078Y00_formula : nativeHeat078Y00 = nativeHeat078Frames.y := by
  decide +kernel

theorem nativeHeat078All48 : nativeHeatPasses nativeGap079Old nativeHeat078Frames nativeHeat078Coef nativeHeat078Fixed nativeHeat078Base 48 nativeHeat078Frames.y = nativeHeat078Y48 := by
  rw [← nativeHeat078Y00_formula]
  have h4 : nativeHeatPasses nativeGap079Old nativeHeat078Frames nativeHeat078Coef nativeHeat078Fixed nativeHeat078Base 4 nativeHeat078Y00 = nativeHeat078Y04 := nativeHeat078Pass04
  have h8 : nativeHeatPasses nativeGap079Old nativeHeat078Frames nativeHeat078Coef nativeHeat078Fixed nativeHeat078Base 8 nativeHeat078Y00 = nativeHeat078Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat078Pass08]
  have h12 : nativeHeatPasses nativeGap079Old nativeHeat078Frames nativeHeat078Coef nativeHeat078Fixed nativeHeat078Base 12 nativeHeat078Y00 = nativeHeat078Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat078Pass12]
  have h16 : nativeHeatPasses nativeGap079Old nativeHeat078Frames nativeHeat078Coef nativeHeat078Fixed nativeHeat078Base 16 nativeHeat078Y00 = nativeHeat078Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat078Pass16]
  have h20 : nativeHeatPasses nativeGap079Old nativeHeat078Frames nativeHeat078Coef nativeHeat078Fixed nativeHeat078Base 20 nativeHeat078Y00 = nativeHeat078Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat078Pass20]
  have h24 : nativeHeatPasses nativeGap079Old nativeHeat078Frames nativeHeat078Coef nativeHeat078Fixed nativeHeat078Base 24 nativeHeat078Y00 = nativeHeat078Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat078Pass24]
  have h28 : nativeHeatPasses nativeGap079Old nativeHeat078Frames nativeHeat078Coef nativeHeat078Fixed nativeHeat078Base 28 nativeHeat078Y00 = nativeHeat078Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat078Pass28]
  have h32 : nativeHeatPasses nativeGap079Old nativeHeat078Frames nativeHeat078Coef nativeHeat078Fixed nativeHeat078Base 32 nativeHeat078Y00 = nativeHeat078Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat078Pass32]
  have h36 : nativeHeatPasses nativeGap079Old nativeHeat078Frames nativeHeat078Coef nativeHeat078Fixed nativeHeat078Base 36 nativeHeat078Y00 = nativeHeat078Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat078Pass36]
  have h40 : nativeHeatPasses nativeGap079Old nativeHeat078Frames nativeHeat078Coef nativeHeat078Fixed nativeHeat078Base 40 nativeHeat078Y00 = nativeHeat078Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat078Pass40]
  have h44 : nativeHeatPasses nativeGap079Old nativeHeat078Frames nativeHeat078Coef nativeHeat078Fixed nativeHeat078Base 44 nativeHeat078Y00 = nativeHeat078Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat078Pass44]
  have h48 : nativeHeatPasses nativeGap079Old nativeHeat078Frames nativeHeat078Coef nativeHeat078Fixed nativeHeat078Base 48 nativeHeat078Y00 = nativeHeat078Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat078Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
