module
public import ASDExplicitGamma.Numerics.Native.Heat103Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat103Y00_formula : nativeHeat103Y00 = nativeHeat103Frames.y := by
  decide +kernel

theorem nativeHeat103All48 : nativeHeatPasses nativeGap104Old nativeHeat103Frames nativeHeat103Coef nativeHeat103Fixed nativeHeat103Base 48 nativeHeat103Frames.y = nativeHeat103Y48 := by
  rw [← nativeHeat103Y00_formula]
  have h4 : nativeHeatPasses nativeGap104Old nativeHeat103Frames nativeHeat103Coef nativeHeat103Fixed nativeHeat103Base 4 nativeHeat103Y00 = nativeHeat103Y04 := nativeHeat103Pass04
  have h8 : nativeHeatPasses nativeGap104Old nativeHeat103Frames nativeHeat103Coef nativeHeat103Fixed nativeHeat103Base 8 nativeHeat103Y00 = nativeHeat103Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat103Pass08]
  have h12 : nativeHeatPasses nativeGap104Old nativeHeat103Frames nativeHeat103Coef nativeHeat103Fixed nativeHeat103Base 12 nativeHeat103Y00 = nativeHeat103Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat103Pass12]
  have h16 : nativeHeatPasses nativeGap104Old nativeHeat103Frames nativeHeat103Coef nativeHeat103Fixed nativeHeat103Base 16 nativeHeat103Y00 = nativeHeat103Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat103Pass16]
  have h20 : nativeHeatPasses nativeGap104Old nativeHeat103Frames nativeHeat103Coef nativeHeat103Fixed nativeHeat103Base 20 nativeHeat103Y00 = nativeHeat103Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat103Pass20]
  have h24 : nativeHeatPasses nativeGap104Old nativeHeat103Frames nativeHeat103Coef nativeHeat103Fixed nativeHeat103Base 24 nativeHeat103Y00 = nativeHeat103Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat103Pass24]
  have h28 : nativeHeatPasses nativeGap104Old nativeHeat103Frames nativeHeat103Coef nativeHeat103Fixed nativeHeat103Base 28 nativeHeat103Y00 = nativeHeat103Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat103Pass28]
  have h32 : nativeHeatPasses nativeGap104Old nativeHeat103Frames nativeHeat103Coef nativeHeat103Fixed nativeHeat103Base 32 nativeHeat103Y00 = nativeHeat103Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat103Pass32]
  have h36 : nativeHeatPasses nativeGap104Old nativeHeat103Frames nativeHeat103Coef nativeHeat103Fixed nativeHeat103Base 36 nativeHeat103Y00 = nativeHeat103Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat103Pass36]
  have h40 : nativeHeatPasses nativeGap104Old nativeHeat103Frames nativeHeat103Coef nativeHeat103Fixed nativeHeat103Base 40 nativeHeat103Y00 = nativeHeat103Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat103Pass40]
  have h44 : nativeHeatPasses nativeGap104Old nativeHeat103Frames nativeHeat103Coef nativeHeat103Fixed nativeHeat103Base 44 nativeHeat103Y00 = nativeHeat103Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat103Pass44]
  have h48 : nativeHeatPasses nativeGap104Old nativeHeat103Frames nativeHeat103Coef nativeHeat103Fixed nativeHeat103Base 48 nativeHeat103Y00 = nativeHeat103Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat103Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
