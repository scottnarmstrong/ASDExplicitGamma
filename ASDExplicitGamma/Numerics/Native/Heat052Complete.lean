module
public import ASDExplicitGamma.Numerics.Native.Heat052Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat052Y00_formula : nativeHeat052Y00 = nativeHeat052Frames.y := by
  decide +kernel

theorem nativeHeat052All48 : nativeHeatPasses nativeGap053Old nativeHeat052Frames nativeHeat052Coef nativeHeat052Fixed nativeHeat052Base 48 nativeHeat052Frames.y = nativeHeat052Y48 := by
  rw [← nativeHeat052Y00_formula]
  have h4 : nativeHeatPasses nativeGap053Old nativeHeat052Frames nativeHeat052Coef nativeHeat052Fixed nativeHeat052Base 4 nativeHeat052Y00 = nativeHeat052Y04 := nativeHeat052Pass04
  have h8 : nativeHeatPasses nativeGap053Old nativeHeat052Frames nativeHeat052Coef nativeHeat052Fixed nativeHeat052Base 8 nativeHeat052Y00 = nativeHeat052Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat052Pass08]
  have h12 : nativeHeatPasses nativeGap053Old nativeHeat052Frames nativeHeat052Coef nativeHeat052Fixed nativeHeat052Base 12 nativeHeat052Y00 = nativeHeat052Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat052Pass12]
  have h16 : nativeHeatPasses nativeGap053Old nativeHeat052Frames nativeHeat052Coef nativeHeat052Fixed nativeHeat052Base 16 nativeHeat052Y00 = nativeHeat052Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat052Pass16]
  have h20 : nativeHeatPasses nativeGap053Old nativeHeat052Frames nativeHeat052Coef nativeHeat052Fixed nativeHeat052Base 20 nativeHeat052Y00 = nativeHeat052Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat052Pass20]
  have h24 : nativeHeatPasses nativeGap053Old nativeHeat052Frames nativeHeat052Coef nativeHeat052Fixed nativeHeat052Base 24 nativeHeat052Y00 = nativeHeat052Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat052Pass24]
  have h28 : nativeHeatPasses nativeGap053Old nativeHeat052Frames nativeHeat052Coef nativeHeat052Fixed nativeHeat052Base 28 nativeHeat052Y00 = nativeHeat052Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat052Pass28]
  have h32 : nativeHeatPasses nativeGap053Old nativeHeat052Frames nativeHeat052Coef nativeHeat052Fixed nativeHeat052Base 32 nativeHeat052Y00 = nativeHeat052Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat052Pass32]
  have h36 : nativeHeatPasses nativeGap053Old nativeHeat052Frames nativeHeat052Coef nativeHeat052Fixed nativeHeat052Base 36 nativeHeat052Y00 = nativeHeat052Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat052Pass36]
  have h40 : nativeHeatPasses nativeGap053Old nativeHeat052Frames nativeHeat052Coef nativeHeat052Fixed nativeHeat052Base 40 nativeHeat052Y00 = nativeHeat052Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat052Pass40]
  have h44 : nativeHeatPasses nativeGap053Old nativeHeat052Frames nativeHeat052Coef nativeHeat052Fixed nativeHeat052Base 44 nativeHeat052Y00 = nativeHeat052Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat052Pass44]
  have h48 : nativeHeatPasses nativeGap053Old nativeHeat052Frames nativeHeat052Coef nativeHeat052Fixed nativeHeat052Base 48 nativeHeat052Y00 = nativeHeat052Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat052Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
