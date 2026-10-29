module
public import ASDExplicitGamma.Numerics.Native.Heat009Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat009Y00_formula : nativeHeat009Y00 = nativeHeat009Frames.y := by
  decide +kernel

theorem nativeHeat009All48 : nativeHeatPasses nativeGap010Old nativeHeat009Frames nativeHeat009Coef nativeHeat009Fixed nativeHeat009Base 48 nativeHeat009Frames.y = nativeHeat009Y48 := by
  rw [← nativeHeat009Y00_formula]
  have h4 : nativeHeatPasses nativeGap010Old nativeHeat009Frames nativeHeat009Coef nativeHeat009Fixed nativeHeat009Base 4 nativeHeat009Y00 = nativeHeat009Y04 := nativeHeat009Pass04
  have h8 : nativeHeatPasses nativeGap010Old nativeHeat009Frames nativeHeat009Coef nativeHeat009Fixed nativeHeat009Base 8 nativeHeat009Y00 = nativeHeat009Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat009Pass08]
  have h12 : nativeHeatPasses nativeGap010Old nativeHeat009Frames nativeHeat009Coef nativeHeat009Fixed nativeHeat009Base 12 nativeHeat009Y00 = nativeHeat009Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat009Pass12]
  have h16 : nativeHeatPasses nativeGap010Old nativeHeat009Frames nativeHeat009Coef nativeHeat009Fixed nativeHeat009Base 16 nativeHeat009Y00 = nativeHeat009Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat009Pass16]
  have h20 : nativeHeatPasses nativeGap010Old nativeHeat009Frames nativeHeat009Coef nativeHeat009Fixed nativeHeat009Base 20 nativeHeat009Y00 = nativeHeat009Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat009Pass20]
  have h24 : nativeHeatPasses nativeGap010Old nativeHeat009Frames nativeHeat009Coef nativeHeat009Fixed nativeHeat009Base 24 nativeHeat009Y00 = nativeHeat009Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat009Pass24]
  have h28 : nativeHeatPasses nativeGap010Old nativeHeat009Frames nativeHeat009Coef nativeHeat009Fixed nativeHeat009Base 28 nativeHeat009Y00 = nativeHeat009Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat009Pass28]
  have h32 : nativeHeatPasses nativeGap010Old nativeHeat009Frames nativeHeat009Coef nativeHeat009Fixed nativeHeat009Base 32 nativeHeat009Y00 = nativeHeat009Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat009Pass32]
  have h36 : nativeHeatPasses nativeGap010Old nativeHeat009Frames nativeHeat009Coef nativeHeat009Fixed nativeHeat009Base 36 nativeHeat009Y00 = nativeHeat009Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat009Pass36]
  have h40 : nativeHeatPasses nativeGap010Old nativeHeat009Frames nativeHeat009Coef nativeHeat009Fixed nativeHeat009Base 40 nativeHeat009Y00 = nativeHeat009Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat009Pass40]
  have h44 : nativeHeatPasses nativeGap010Old nativeHeat009Frames nativeHeat009Coef nativeHeat009Fixed nativeHeat009Base 44 nativeHeat009Y00 = nativeHeat009Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat009Pass44]
  have h48 : nativeHeatPasses nativeGap010Old nativeHeat009Frames nativeHeat009Coef nativeHeat009Fixed nativeHeat009Base 48 nativeHeat009Y00 = nativeHeat009Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat009Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
