module
public import ASDExplicitGamma.Numerics.Native.Heat011Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat011Y00_formula : nativeHeat011Y00 = nativeHeat011Frames.y := by
  decide +kernel

theorem nativeHeat011All48 : nativeHeatPasses nativeGap012Old nativeHeat011Frames nativeHeat011Coef nativeHeat011Fixed nativeHeat011Base 48 nativeHeat011Frames.y = nativeHeat011Y48 := by
  rw [← nativeHeat011Y00_formula]
  have h4 : nativeHeatPasses nativeGap012Old nativeHeat011Frames nativeHeat011Coef nativeHeat011Fixed nativeHeat011Base 4 nativeHeat011Y00 = nativeHeat011Y04 := nativeHeat011Pass04
  have h8 : nativeHeatPasses nativeGap012Old nativeHeat011Frames nativeHeat011Coef nativeHeat011Fixed nativeHeat011Base 8 nativeHeat011Y00 = nativeHeat011Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat011Pass08]
  have h12 : nativeHeatPasses nativeGap012Old nativeHeat011Frames nativeHeat011Coef nativeHeat011Fixed nativeHeat011Base 12 nativeHeat011Y00 = nativeHeat011Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat011Pass12]
  have h16 : nativeHeatPasses nativeGap012Old nativeHeat011Frames nativeHeat011Coef nativeHeat011Fixed nativeHeat011Base 16 nativeHeat011Y00 = nativeHeat011Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat011Pass16]
  have h20 : nativeHeatPasses nativeGap012Old nativeHeat011Frames nativeHeat011Coef nativeHeat011Fixed nativeHeat011Base 20 nativeHeat011Y00 = nativeHeat011Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat011Pass20]
  have h24 : nativeHeatPasses nativeGap012Old nativeHeat011Frames nativeHeat011Coef nativeHeat011Fixed nativeHeat011Base 24 nativeHeat011Y00 = nativeHeat011Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat011Pass24]
  have h28 : nativeHeatPasses nativeGap012Old nativeHeat011Frames nativeHeat011Coef nativeHeat011Fixed nativeHeat011Base 28 nativeHeat011Y00 = nativeHeat011Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat011Pass28]
  have h32 : nativeHeatPasses nativeGap012Old nativeHeat011Frames nativeHeat011Coef nativeHeat011Fixed nativeHeat011Base 32 nativeHeat011Y00 = nativeHeat011Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat011Pass32]
  have h36 : nativeHeatPasses nativeGap012Old nativeHeat011Frames nativeHeat011Coef nativeHeat011Fixed nativeHeat011Base 36 nativeHeat011Y00 = nativeHeat011Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat011Pass36]
  have h40 : nativeHeatPasses nativeGap012Old nativeHeat011Frames nativeHeat011Coef nativeHeat011Fixed nativeHeat011Base 40 nativeHeat011Y00 = nativeHeat011Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat011Pass40]
  have h44 : nativeHeatPasses nativeGap012Old nativeHeat011Frames nativeHeat011Coef nativeHeat011Fixed nativeHeat011Base 44 nativeHeat011Y00 = nativeHeat011Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat011Pass44]
  have h48 : nativeHeatPasses nativeGap012Old nativeHeat011Frames nativeHeat011Coef nativeHeat011Fixed nativeHeat011Base 48 nativeHeat011Y00 = nativeHeat011Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat011Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
