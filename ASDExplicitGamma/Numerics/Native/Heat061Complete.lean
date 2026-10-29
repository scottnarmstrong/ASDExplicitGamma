module
public import ASDExplicitGamma.Numerics.Native.Heat061Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat061Y00_formula : nativeHeat061Y00 = nativeHeat061Frames.y := by
  decide +kernel

theorem nativeHeat061All48 : nativeHeatPasses nativeGap062Old nativeHeat061Frames nativeHeat061Coef nativeHeat061Fixed nativeHeat061Base 48 nativeHeat061Frames.y = nativeHeat061Y48 := by
  rw [← nativeHeat061Y00_formula]
  have h4 : nativeHeatPasses nativeGap062Old nativeHeat061Frames nativeHeat061Coef nativeHeat061Fixed nativeHeat061Base 4 nativeHeat061Y00 = nativeHeat061Y04 := nativeHeat061Pass04
  have h8 : nativeHeatPasses nativeGap062Old nativeHeat061Frames nativeHeat061Coef nativeHeat061Fixed nativeHeat061Base 8 nativeHeat061Y00 = nativeHeat061Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat061Pass08]
  have h12 : nativeHeatPasses nativeGap062Old nativeHeat061Frames nativeHeat061Coef nativeHeat061Fixed nativeHeat061Base 12 nativeHeat061Y00 = nativeHeat061Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat061Pass12]
  have h16 : nativeHeatPasses nativeGap062Old nativeHeat061Frames nativeHeat061Coef nativeHeat061Fixed nativeHeat061Base 16 nativeHeat061Y00 = nativeHeat061Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat061Pass16]
  have h20 : nativeHeatPasses nativeGap062Old nativeHeat061Frames nativeHeat061Coef nativeHeat061Fixed nativeHeat061Base 20 nativeHeat061Y00 = nativeHeat061Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat061Pass20]
  have h24 : nativeHeatPasses nativeGap062Old nativeHeat061Frames nativeHeat061Coef nativeHeat061Fixed nativeHeat061Base 24 nativeHeat061Y00 = nativeHeat061Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat061Pass24]
  have h28 : nativeHeatPasses nativeGap062Old nativeHeat061Frames nativeHeat061Coef nativeHeat061Fixed nativeHeat061Base 28 nativeHeat061Y00 = nativeHeat061Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat061Pass28]
  have h32 : nativeHeatPasses nativeGap062Old nativeHeat061Frames nativeHeat061Coef nativeHeat061Fixed nativeHeat061Base 32 nativeHeat061Y00 = nativeHeat061Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat061Pass32]
  have h36 : nativeHeatPasses nativeGap062Old nativeHeat061Frames nativeHeat061Coef nativeHeat061Fixed nativeHeat061Base 36 nativeHeat061Y00 = nativeHeat061Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat061Pass36]
  have h40 : nativeHeatPasses nativeGap062Old nativeHeat061Frames nativeHeat061Coef nativeHeat061Fixed nativeHeat061Base 40 nativeHeat061Y00 = nativeHeat061Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat061Pass40]
  have h44 : nativeHeatPasses nativeGap062Old nativeHeat061Frames nativeHeat061Coef nativeHeat061Fixed nativeHeat061Base 44 nativeHeat061Y00 = nativeHeat061Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat061Pass44]
  have h48 : nativeHeatPasses nativeGap062Old nativeHeat061Frames nativeHeat061Coef nativeHeat061Fixed nativeHeat061Base 48 nativeHeat061Y00 = nativeHeat061Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat061Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
