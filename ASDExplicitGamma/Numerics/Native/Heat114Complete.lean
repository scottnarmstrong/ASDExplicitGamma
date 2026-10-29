module
public import ASDExplicitGamma.Numerics.Native.Heat114Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat114Y00_formula : nativeHeat114Y00 = nativeHeat114Frames.y := by
  decide +kernel

theorem nativeHeat114All48 : nativeHeatPasses nativeGap115Old nativeHeat114Frames nativeHeat114Coef nativeHeat114Fixed nativeHeat114Base 48 nativeHeat114Frames.y = nativeHeat114Y48 := by
  rw [← nativeHeat114Y00_formula]
  have h4 : nativeHeatPasses nativeGap115Old nativeHeat114Frames nativeHeat114Coef nativeHeat114Fixed nativeHeat114Base 4 nativeHeat114Y00 = nativeHeat114Y04 := nativeHeat114Pass04
  have h8 : nativeHeatPasses nativeGap115Old nativeHeat114Frames nativeHeat114Coef nativeHeat114Fixed nativeHeat114Base 8 nativeHeat114Y00 = nativeHeat114Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat114Pass08]
  have h12 : nativeHeatPasses nativeGap115Old nativeHeat114Frames nativeHeat114Coef nativeHeat114Fixed nativeHeat114Base 12 nativeHeat114Y00 = nativeHeat114Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat114Pass12]
  have h16 : nativeHeatPasses nativeGap115Old nativeHeat114Frames nativeHeat114Coef nativeHeat114Fixed nativeHeat114Base 16 nativeHeat114Y00 = nativeHeat114Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat114Pass16]
  have h20 : nativeHeatPasses nativeGap115Old nativeHeat114Frames nativeHeat114Coef nativeHeat114Fixed nativeHeat114Base 20 nativeHeat114Y00 = nativeHeat114Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat114Pass20]
  have h24 : nativeHeatPasses nativeGap115Old nativeHeat114Frames nativeHeat114Coef nativeHeat114Fixed nativeHeat114Base 24 nativeHeat114Y00 = nativeHeat114Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat114Pass24]
  have h28 : nativeHeatPasses nativeGap115Old nativeHeat114Frames nativeHeat114Coef nativeHeat114Fixed nativeHeat114Base 28 nativeHeat114Y00 = nativeHeat114Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat114Pass28]
  have h32 : nativeHeatPasses nativeGap115Old nativeHeat114Frames nativeHeat114Coef nativeHeat114Fixed nativeHeat114Base 32 nativeHeat114Y00 = nativeHeat114Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat114Pass32]
  have h36 : nativeHeatPasses nativeGap115Old nativeHeat114Frames nativeHeat114Coef nativeHeat114Fixed nativeHeat114Base 36 nativeHeat114Y00 = nativeHeat114Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat114Pass36]
  have h40 : nativeHeatPasses nativeGap115Old nativeHeat114Frames nativeHeat114Coef nativeHeat114Fixed nativeHeat114Base 40 nativeHeat114Y00 = nativeHeat114Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat114Pass40]
  have h44 : nativeHeatPasses nativeGap115Old nativeHeat114Frames nativeHeat114Coef nativeHeat114Fixed nativeHeat114Base 44 nativeHeat114Y00 = nativeHeat114Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat114Pass44]
  have h48 : nativeHeatPasses nativeGap115Old nativeHeat114Frames nativeHeat114Coef nativeHeat114Fixed nativeHeat114Base 48 nativeHeat114Y00 = nativeHeat114Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat114Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
