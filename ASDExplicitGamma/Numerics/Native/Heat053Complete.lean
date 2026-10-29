module
public import ASDExplicitGamma.Numerics.Native.Heat053Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat053Y00_formula : nativeHeat053Y00 = nativeHeat053Frames.y := by
  decide +kernel

theorem nativeHeat053All48 : nativeHeatPasses nativeGap054Old nativeHeat053Frames nativeHeat053Coef nativeHeat053Fixed nativeHeat053Base 48 nativeHeat053Frames.y = nativeHeat053Y48 := by
  rw [← nativeHeat053Y00_formula]
  have h4 : nativeHeatPasses nativeGap054Old nativeHeat053Frames nativeHeat053Coef nativeHeat053Fixed nativeHeat053Base 4 nativeHeat053Y00 = nativeHeat053Y04 := nativeHeat053Pass04
  have h8 : nativeHeatPasses nativeGap054Old nativeHeat053Frames nativeHeat053Coef nativeHeat053Fixed nativeHeat053Base 8 nativeHeat053Y00 = nativeHeat053Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat053Pass08]
  have h12 : nativeHeatPasses nativeGap054Old nativeHeat053Frames nativeHeat053Coef nativeHeat053Fixed nativeHeat053Base 12 nativeHeat053Y00 = nativeHeat053Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat053Pass12]
  have h16 : nativeHeatPasses nativeGap054Old nativeHeat053Frames nativeHeat053Coef nativeHeat053Fixed nativeHeat053Base 16 nativeHeat053Y00 = nativeHeat053Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat053Pass16]
  have h20 : nativeHeatPasses nativeGap054Old nativeHeat053Frames nativeHeat053Coef nativeHeat053Fixed nativeHeat053Base 20 nativeHeat053Y00 = nativeHeat053Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat053Pass20]
  have h24 : nativeHeatPasses nativeGap054Old nativeHeat053Frames nativeHeat053Coef nativeHeat053Fixed nativeHeat053Base 24 nativeHeat053Y00 = nativeHeat053Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat053Pass24]
  have h28 : nativeHeatPasses nativeGap054Old nativeHeat053Frames nativeHeat053Coef nativeHeat053Fixed nativeHeat053Base 28 nativeHeat053Y00 = nativeHeat053Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat053Pass28]
  have h32 : nativeHeatPasses nativeGap054Old nativeHeat053Frames nativeHeat053Coef nativeHeat053Fixed nativeHeat053Base 32 nativeHeat053Y00 = nativeHeat053Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat053Pass32]
  have h36 : nativeHeatPasses nativeGap054Old nativeHeat053Frames nativeHeat053Coef nativeHeat053Fixed nativeHeat053Base 36 nativeHeat053Y00 = nativeHeat053Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat053Pass36]
  have h40 : nativeHeatPasses nativeGap054Old nativeHeat053Frames nativeHeat053Coef nativeHeat053Fixed nativeHeat053Base 40 nativeHeat053Y00 = nativeHeat053Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat053Pass40]
  have h44 : nativeHeatPasses nativeGap054Old nativeHeat053Frames nativeHeat053Coef nativeHeat053Fixed nativeHeat053Base 44 nativeHeat053Y00 = nativeHeat053Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat053Pass44]
  have h48 : nativeHeatPasses nativeGap054Old nativeHeat053Frames nativeHeat053Coef nativeHeat053Fixed nativeHeat053Base 48 nativeHeat053Y00 = nativeHeat053Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat053Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
