module
public import ASDExplicitGamma.Numerics.Native.Heat125Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat125Y00_formula : nativeHeat125Y00 = nativeHeat125Frames.y := by
  decide +kernel

theorem nativeHeat125All48 : nativeHeatPasses nativeGap126Old nativeHeat125Frames nativeHeat125Coef nativeHeat125Fixed nativeHeat125Base 48 nativeHeat125Frames.y = nativeHeat125Y48 := by
  rw [← nativeHeat125Y00_formula]
  have h4 : nativeHeatPasses nativeGap126Old nativeHeat125Frames nativeHeat125Coef nativeHeat125Fixed nativeHeat125Base 4 nativeHeat125Y00 = nativeHeat125Y04 := nativeHeat125Pass04
  have h8 : nativeHeatPasses nativeGap126Old nativeHeat125Frames nativeHeat125Coef nativeHeat125Fixed nativeHeat125Base 8 nativeHeat125Y00 = nativeHeat125Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat125Pass08]
  have h12 : nativeHeatPasses nativeGap126Old nativeHeat125Frames nativeHeat125Coef nativeHeat125Fixed nativeHeat125Base 12 nativeHeat125Y00 = nativeHeat125Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat125Pass12]
  have h16 : nativeHeatPasses nativeGap126Old nativeHeat125Frames nativeHeat125Coef nativeHeat125Fixed nativeHeat125Base 16 nativeHeat125Y00 = nativeHeat125Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat125Pass16]
  have h20 : nativeHeatPasses nativeGap126Old nativeHeat125Frames nativeHeat125Coef nativeHeat125Fixed nativeHeat125Base 20 nativeHeat125Y00 = nativeHeat125Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat125Pass20]
  have h24 : nativeHeatPasses nativeGap126Old nativeHeat125Frames nativeHeat125Coef nativeHeat125Fixed nativeHeat125Base 24 nativeHeat125Y00 = nativeHeat125Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat125Pass24]
  have h28 : nativeHeatPasses nativeGap126Old nativeHeat125Frames nativeHeat125Coef nativeHeat125Fixed nativeHeat125Base 28 nativeHeat125Y00 = nativeHeat125Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat125Pass28]
  have h32 : nativeHeatPasses nativeGap126Old nativeHeat125Frames nativeHeat125Coef nativeHeat125Fixed nativeHeat125Base 32 nativeHeat125Y00 = nativeHeat125Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat125Pass32]
  have h36 : nativeHeatPasses nativeGap126Old nativeHeat125Frames nativeHeat125Coef nativeHeat125Fixed nativeHeat125Base 36 nativeHeat125Y00 = nativeHeat125Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat125Pass36]
  have h40 : nativeHeatPasses nativeGap126Old nativeHeat125Frames nativeHeat125Coef nativeHeat125Fixed nativeHeat125Base 40 nativeHeat125Y00 = nativeHeat125Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat125Pass40]
  have h44 : nativeHeatPasses nativeGap126Old nativeHeat125Frames nativeHeat125Coef nativeHeat125Fixed nativeHeat125Base 44 nativeHeat125Y00 = nativeHeat125Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat125Pass44]
  have h48 : nativeHeatPasses nativeGap126Old nativeHeat125Frames nativeHeat125Coef nativeHeat125Fixed nativeHeat125Base 48 nativeHeat125Y00 = nativeHeat125Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat125Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
