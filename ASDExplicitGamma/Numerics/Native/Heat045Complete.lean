module
public import ASDExplicitGamma.Numerics.Native.Heat045Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat045Y00_formula : nativeHeat045Y00 = nativeHeat045Frames.y := by
  decide +kernel

theorem nativeHeat045All48 : nativeHeatPasses nativeGap046Old nativeHeat045Frames nativeHeat045Coef nativeHeat045Fixed nativeHeat045Base 48 nativeHeat045Frames.y = nativeHeat045Y48 := by
  rw [← nativeHeat045Y00_formula]
  have h4 : nativeHeatPasses nativeGap046Old nativeHeat045Frames nativeHeat045Coef nativeHeat045Fixed nativeHeat045Base 4 nativeHeat045Y00 = nativeHeat045Y04 := nativeHeat045Pass04
  have h8 : nativeHeatPasses nativeGap046Old nativeHeat045Frames nativeHeat045Coef nativeHeat045Fixed nativeHeat045Base 8 nativeHeat045Y00 = nativeHeat045Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat045Pass08]
  have h12 : nativeHeatPasses nativeGap046Old nativeHeat045Frames nativeHeat045Coef nativeHeat045Fixed nativeHeat045Base 12 nativeHeat045Y00 = nativeHeat045Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat045Pass12]
  have h16 : nativeHeatPasses nativeGap046Old nativeHeat045Frames nativeHeat045Coef nativeHeat045Fixed nativeHeat045Base 16 nativeHeat045Y00 = nativeHeat045Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat045Pass16]
  have h20 : nativeHeatPasses nativeGap046Old nativeHeat045Frames nativeHeat045Coef nativeHeat045Fixed nativeHeat045Base 20 nativeHeat045Y00 = nativeHeat045Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat045Pass20]
  have h24 : nativeHeatPasses nativeGap046Old nativeHeat045Frames nativeHeat045Coef nativeHeat045Fixed nativeHeat045Base 24 nativeHeat045Y00 = nativeHeat045Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat045Pass24]
  have h28 : nativeHeatPasses nativeGap046Old nativeHeat045Frames nativeHeat045Coef nativeHeat045Fixed nativeHeat045Base 28 nativeHeat045Y00 = nativeHeat045Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat045Pass28]
  have h32 : nativeHeatPasses nativeGap046Old nativeHeat045Frames nativeHeat045Coef nativeHeat045Fixed nativeHeat045Base 32 nativeHeat045Y00 = nativeHeat045Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat045Pass32]
  have h36 : nativeHeatPasses nativeGap046Old nativeHeat045Frames nativeHeat045Coef nativeHeat045Fixed nativeHeat045Base 36 nativeHeat045Y00 = nativeHeat045Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat045Pass36]
  have h40 : nativeHeatPasses nativeGap046Old nativeHeat045Frames nativeHeat045Coef nativeHeat045Fixed nativeHeat045Base 40 nativeHeat045Y00 = nativeHeat045Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat045Pass40]
  have h44 : nativeHeatPasses nativeGap046Old nativeHeat045Frames nativeHeat045Coef nativeHeat045Fixed nativeHeat045Base 44 nativeHeat045Y00 = nativeHeat045Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat045Pass44]
  have h48 : nativeHeatPasses nativeGap046Old nativeHeat045Frames nativeHeat045Coef nativeHeat045Fixed nativeHeat045Base 48 nativeHeat045Y00 = nativeHeat045Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat045Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
