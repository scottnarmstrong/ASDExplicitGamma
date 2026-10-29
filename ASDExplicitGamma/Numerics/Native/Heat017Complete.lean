module
public import ASDExplicitGamma.Numerics.Native.Heat017Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat017Y00_formula : nativeHeat017Y00 = nativeHeat017Frames.y := by
  decide +kernel

theorem nativeHeat017All48 : nativeHeatPasses nativeGap018Old nativeHeat017Frames nativeHeat017Coef nativeHeat017Fixed nativeHeat017Base 48 nativeHeat017Frames.y = nativeHeat017Y48 := by
  rw [← nativeHeat017Y00_formula]
  have h4 : nativeHeatPasses nativeGap018Old nativeHeat017Frames nativeHeat017Coef nativeHeat017Fixed nativeHeat017Base 4 nativeHeat017Y00 = nativeHeat017Y04 := nativeHeat017Pass04
  have h8 : nativeHeatPasses nativeGap018Old nativeHeat017Frames nativeHeat017Coef nativeHeat017Fixed nativeHeat017Base 8 nativeHeat017Y00 = nativeHeat017Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat017Pass08]
  have h12 : nativeHeatPasses nativeGap018Old nativeHeat017Frames nativeHeat017Coef nativeHeat017Fixed nativeHeat017Base 12 nativeHeat017Y00 = nativeHeat017Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat017Pass12]
  have h16 : nativeHeatPasses nativeGap018Old nativeHeat017Frames nativeHeat017Coef nativeHeat017Fixed nativeHeat017Base 16 nativeHeat017Y00 = nativeHeat017Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat017Pass16]
  have h20 : nativeHeatPasses nativeGap018Old nativeHeat017Frames nativeHeat017Coef nativeHeat017Fixed nativeHeat017Base 20 nativeHeat017Y00 = nativeHeat017Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat017Pass20]
  have h24 : nativeHeatPasses nativeGap018Old nativeHeat017Frames nativeHeat017Coef nativeHeat017Fixed nativeHeat017Base 24 nativeHeat017Y00 = nativeHeat017Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat017Pass24]
  have h28 : nativeHeatPasses nativeGap018Old nativeHeat017Frames nativeHeat017Coef nativeHeat017Fixed nativeHeat017Base 28 nativeHeat017Y00 = nativeHeat017Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat017Pass28]
  have h32 : nativeHeatPasses nativeGap018Old nativeHeat017Frames nativeHeat017Coef nativeHeat017Fixed nativeHeat017Base 32 nativeHeat017Y00 = nativeHeat017Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat017Pass32]
  have h36 : nativeHeatPasses nativeGap018Old nativeHeat017Frames nativeHeat017Coef nativeHeat017Fixed nativeHeat017Base 36 nativeHeat017Y00 = nativeHeat017Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat017Pass36]
  have h40 : nativeHeatPasses nativeGap018Old nativeHeat017Frames nativeHeat017Coef nativeHeat017Fixed nativeHeat017Base 40 nativeHeat017Y00 = nativeHeat017Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat017Pass40]
  have h44 : nativeHeatPasses nativeGap018Old nativeHeat017Frames nativeHeat017Coef nativeHeat017Fixed nativeHeat017Base 44 nativeHeat017Y00 = nativeHeat017Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat017Pass44]
  have h48 : nativeHeatPasses nativeGap018Old nativeHeat017Frames nativeHeat017Coef nativeHeat017Fixed nativeHeat017Base 48 nativeHeat017Y00 = nativeHeat017Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat017Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
