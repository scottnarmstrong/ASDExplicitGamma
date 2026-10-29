module
public import ASDExplicitGamma.Numerics.Native.Heat116Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat116Y00_formula : nativeHeat116Y00 = nativeHeat116Frames.y := by
  decide +kernel

theorem nativeHeat116All48 : nativeHeatPasses nativeGap117Old nativeHeat116Frames nativeHeat116Coef nativeHeat116Fixed nativeHeat116Base 48 nativeHeat116Frames.y = nativeHeat116Y48 := by
  rw [← nativeHeat116Y00_formula]
  have h4 : nativeHeatPasses nativeGap117Old nativeHeat116Frames nativeHeat116Coef nativeHeat116Fixed nativeHeat116Base 4 nativeHeat116Y00 = nativeHeat116Y04 := nativeHeat116Pass04
  have h8 : nativeHeatPasses nativeGap117Old nativeHeat116Frames nativeHeat116Coef nativeHeat116Fixed nativeHeat116Base 8 nativeHeat116Y00 = nativeHeat116Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat116Pass08]
  have h12 : nativeHeatPasses nativeGap117Old nativeHeat116Frames nativeHeat116Coef nativeHeat116Fixed nativeHeat116Base 12 nativeHeat116Y00 = nativeHeat116Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat116Pass12]
  have h16 : nativeHeatPasses nativeGap117Old nativeHeat116Frames nativeHeat116Coef nativeHeat116Fixed nativeHeat116Base 16 nativeHeat116Y00 = nativeHeat116Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat116Pass16]
  have h20 : nativeHeatPasses nativeGap117Old nativeHeat116Frames nativeHeat116Coef nativeHeat116Fixed nativeHeat116Base 20 nativeHeat116Y00 = nativeHeat116Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat116Pass20]
  have h24 : nativeHeatPasses nativeGap117Old nativeHeat116Frames nativeHeat116Coef nativeHeat116Fixed nativeHeat116Base 24 nativeHeat116Y00 = nativeHeat116Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat116Pass24]
  have h28 : nativeHeatPasses nativeGap117Old nativeHeat116Frames nativeHeat116Coef nativeHeat116Fixed nativeHeat116Base 28 nativeHeat116Y00 = nativeHeat116Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat116Pass28]
  have h32 : nativeHeatPasses nativeGap117Old nativeHeat116Frames nativeHeat116Coef nativeHeat116Fixed nativeHeat116Base 32 nativeHeat116Y00 = nativeHeat116Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat116Pass32]
  have h36 : nativeHeatPasses nativeGap117Old nativeHeat116Frames nativeHeat116Coef nativeHeat116Fixed nativeHeat116Base 36 nativeHeat116Y00 = nativeHeat116Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat116Pass36]
  have h40 : nativeHeatPasses nativeGap117Old nativeHeat116Frames nativeHeat116Coef nativeHeat116Fixed nativeHeat116Base 40 nativeHeat116Y00 = nativeHeat116Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat116Pass40]
  have h44 : nativeHeatPasses nativeGap117Old nativeHeat116Frames nativeHeat116Coef nativeHeat116Fixed nativeHeat116Base 44 nativeHeat116Y00 = nativeHeat116Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat116Pass44]
  have h48 : nativeHeatPasses nativeGap117Old nativeHeat116Frames nativeHeat116Coef nativeHeat116Fixed nativeHeat116Base 48 nativeHeat116Y00 = nativeHeat116Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat116Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
