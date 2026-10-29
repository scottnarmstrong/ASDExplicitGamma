module
public import ASDExplicitGamma.Numerics.Native.Heat027Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat027Y00_formula : nativeHeat027Y00 = nativeHeat027Frames.y := by
  decide +kernel

theorem nativeHeat027All48 : nativeHeatPasses nativeGap028Old nativeHeat027Frames nativeHeat027Coef nativeHeat027Fixed nativeHeat027Base 48 nativeHeat027Frames.y = nativeHeat027Y48 := by
  rw [← nativeHeat027Y00_formula]
  have h4 : nativeHeatPasses nativeGap028Old nativeHeat027Frames nativeHeat027Coef nativeHeat027Fixed nativeHeat027Base 4 nativeHeat027Y00 = nativeHeat027Y04 := nativeHeat027Pass04
  have h8 : nativeHeatPasses nativeGap028Old nativeHeat027Frames nativeHeat027Coef nativeHeat027Fixed nativeHeat027Base 8 nativeHeat027Y00 = nativeHeat027Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat027Pass08]
  have h12 : nativeHeatPasses nativeGap028Old nativeHeat027Frames nativeHeat027Coef nativeHeat027Fixed nativeHeat027Base 12 nativeHeat027Y00 = nativeHeat027Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat027Pass12]
  have h16 : nativeHeatPasses nativeGap028Old nativeHeat027Frames nativeHeat027Coef nativeHeat027Fixed nativeHeat027Base 16 nativeHeat027Y00 = nativeHeat027Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat027Pass16]
  have h20 : nativeHeatPasses nativeGap028Old nativeHeat027Frames nativeHeat027Coef nativeHeat027Fixed nativeHeat027Base 20 nativeHeat027Y00 = nativeHeat027Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat027Pass20]
  have h24 : nativeHeatPasses nativeGap028Old nativeHeat027Frames nativeHeat027Coef nativeHeat027Fixed nativeHeat027Base 24 nativeHeat027Y00 = nativeHeat027Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat027Pass24]
  have h28 : nativeHeatPasses nativeGap028Old nativeHeat027Frames nativeHeat027Coef nativeHeat027Fixed nativeHeat027Base 28 nativeHeat027Y00 = nativeHeat027Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat027Pass28]
  have h32 : nativeHeatPasses nativeGap028Old nativeHeat027Frames nativeHeat027Coef nativeHeat027Fixed nativeHeat027Base 32 nativeHeat027Y00 = nativeHeat027Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat027Pass32]
  have h36 : nativeHeatPasses nativeGap028Old nativeHeat027Frames nativeHeat027Coef nativeHeat027Fixed nativeHeat027Base 36 nativeHeat027Y00 = nativeHeat027Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat027Pass36]
  have h40 : nativeHeatPasses nativeGap028Old nativeHeat027Frames nativeHeat027Coef nativeHeat027Fixed nativeHeat027Base 40 nativeHeat027Y00 = nativeHeat027Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat027Pass40]
  have h44 : nativeHeatPasses nativeGap028Old nativeHeat027Frames nativeHeat027Coef nativeHeat027Fixed nativeHeat027Base 44 nativeHeat027Y00 = nativeHeat027Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat027Pass44]
  have h48 : nativeHeatPasses nativeGap028Old nativeHeat027Frames nativeHeat027Coef nativeHeat027Fixed nativeHeat027Base 48 nativeHeat027Y00 = nativeHeat027Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat027Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
