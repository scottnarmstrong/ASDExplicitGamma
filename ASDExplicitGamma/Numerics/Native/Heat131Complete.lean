module
public import ASDExplicitGamma.Numerics.Native.Heat131Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat131Y00_formula : nativeHeat131Y00 = nativeHeat131Frames.y := by
  decide +kernel

theorem nativeHeat131All48 : nativeHeatPasses nativeGap132Old nativeHeat131Frames nativeHeat131Coef nativeHeat131Fixed nativeHeat131Base 48 nativeHeat131Frames.y = nativeHeat131Y48 := by
  rw [← nativeHeat131Y00_formula]
  have h4 : nativeHeatPasses nativeGap132Old nativeHeat131Frames nativeHeat131Coef nativeHeat131Fixed nativeHeat131Base 4 nativeHeat131Y00 = nativeHeat131Y04 := nativeHeat131Pass04
  have h8 : nativeHeatPasses nativeGap132Old nativeHeat131Frames nativeHeat131Coef nativeHeat131Fixed nativeHeat131Base 8 nativeHeat131Y00 = nativeHeat131Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat131Pass08]
  have h12 : nativeHeatPasses nativeGap132Old nativeHeat131Frames nativeHeat131Coef nativeHeat131Fixed nativeHeat131Base 12 nativeHeat131Y00 = nativeHeat131Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat131Pass12]
  have h16 : nativeHeatPasses nativeGap132Old nativeHeat131Frames nativeHeat131Coef nativeHeat131Fixed nativeHeat131Base 16 nativeHeat131Y00 = nativeHeat131Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat131Pass16]
  have h20 : nativeHeatPasses nativeGap132Old nativeHeat131Frames nativeHeat131Coef nativeHeat131Fixed nativeHeat131Base 20 nativeHeat131Y00 = nativeHeat131Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat131Pass20]
  have h24 : nativeHeatPasses nativeGap132Old nativeHeat131Frames nativeHeat131Coef nativeHeat131Fixed nativeHeat131Base 24 nativeHeat131Y00 = nativeHeat131Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat131Pass24]
  have h28 : nativeHeatPasses nativeGap132Old nativeHeat131Frames nativeHeat131Coef nativeHeat131Fixed nativeHeat131Base 28 nativeHeat131Y00 = nativeHeat131Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat131Pass28]
  have h32 : nativeHeatPasses nativeGap132Old nativeHeat131Frames nativeHeat131Coef nativeHeat131Fixed nativeHeat131Base 32 nativeHeat131Y00 = nativeHeat131Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat131Pass32]
  have h36 : nativeHeatPasses nativeGap132Old nativeHeat131Frames nativeHeat131Coef nativeHeat131Fixed nativeHeat131Base 36 nativeHeat131Y00 = nativeHeat131Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat131Pass36]
  have h40 : nativeHeatPasses nativeGap132Old nativeHeat131Frames nativeHeat131Coef nativeHeat131Fixed nativeHeat131Base 40 nativeHeat131Y00 = nativeHeat131Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat131Pass40]
  have h44 : nativeHeatPasses nativeGap132Old nativeHeat131Frames nativeHeat131Coef nativeHeat131Fixed nativeHeat131Base 44 nativeHeat131Y00 = nativeHeat131Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat131Pass44]
  have h48 : nativeHeatPasses nativeGap132Old nativeHeat131Frames nativeHeat131Coef nativeHeat131Fixed nativeHeat131Base 48 nativeHeat131Y00 = nativeHeat131Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat131Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
