module
public import ASDExplicitGamma.Numerics.Native.Heat147Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat147Y00_formula : nativeHeat147Y00 = nativeHeat147Frames.y := by
  decide +kernel

theorem nativeHeat147All48 : nativeHeatPasses nativeGap148Old nativeHeat147Frames nativeHeat147Coef nativeHeat147Fixed nativeHeat147Base 48 nativeHeat147Frames.y = nativeHeat147Y48 := by
  rw [← nativeHeat147Y00_formula]
  have h4 : nativeHeatPasses nativeGap148Old nativeHeat147Frames nativeHeat147Coef nativeHeat147Fixed nativeHeat147Base 4 nativeHeat147Y00 = nativeHeat147Y04 := nativeHeat147Pass04
  have h8 : nativeHeatPasses nativeGap148Old nativeHeat147Frames nativeHeat147Coef nativeHeat147Fixed nativeHeat147Base 8 nativeHeat147Y00 = nativeHeat147Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat147Pass08]
  have h12 : nativeHeatPasses nativeGap148Old nativeHeat147Frames nativeHeat147Coef nativeHeat147Fixed nativeHeat147Base 12 nativeHeat147Y00 = nativeHeat147Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat147Pass12]
  have h16 : nativeHeatPasses nativeGap148Old nativeHeat147Frames nativeHeat147Coef nativeHeat147Fixed nativeHeat147Base 16 nativeHeat147Y00 = nativeHeat147Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat147Pass16]
  have h20 : nativeHeatPasses nativeGap148Old nativeHeat147Frames nativeHeat147Coef nativeHeat147Fixed nativeHeat147Base 20 nativeHeat147Y00 = nativeHeat147Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat147Pass20]
  have h24 : nativeHeatPasses nativeGap148Old nativeHeat147Frames nativeHeat147Coef nativeHeat147Fixed nativeHeat147Base 24 nativeHeat147Y00 = nativeHeat147Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat147Pass24]
  have h28 : nativeHeatPasses nativeGap148Old nativeHeat147Frames nativeHeat147Coef nativeHeat147Fixed nativeHeat147Base 28 nativeHeat147Y00 = nativeHeat147Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat147Pass28]
  have h32 : nativeHeatPasses nativeGap148Old nativeHeat147Frames nativeHeat147Coef nativeHeat147Fixed nativeHeat147Base 32 nativeHeat147Y00 = nativeHeat147Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat147Pass32]
  have h36 : nativeHeatPasses nativeGap148Old nativeHeat147Frames nativeHeat147Coef nativeHeat147Fixed nativeHeat147Base 36 nativeHeat147Y00 = nativeHeat147Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat147Pass36]
  have h40 : nativeHeatPasses nativeGap148Old nativeHeat147Frames nativeHeat147Coef nativeHeat147Fixed nativeHeat147Base 40 nativeHeat147Y00 = nativeHeat147Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat147Pass40]
  have h44 : nativeHeatPasses nativeGap148Old nativeHeat147Frames nativeHeat147Coef nativeHeat147Fixed nativeHeat147Base 44 nativeHeat147Y00 = nativeHeat147Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat147Pass44]
  have h48 : nativeHeatPasses nativeGap148Old nativeHeat147Frames nativeHeat147Coef nativeHeat147Fixed nativeHeat147Base 48 nativeHeat147Y00 = nativeHeat147Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat147Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
