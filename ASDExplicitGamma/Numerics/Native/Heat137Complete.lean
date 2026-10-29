module
public import ASDExplicitGamma.Numerics.Native.Heat137Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat137Y00_formula : nativeHeat137Y00 = nativeHeat137Frames.y := by
  decide +kernel

theorem nativeHeat137All48 : nativeHeatPasses nativeGap138Old nativeHeat137Frames nativeHeat137Coef nativeHeat137Fixed nativeHeat137Base 48 nativeHeat137Frames.y = nativeHeat137Y48 := by
  rw [← nativeHeat137Y00_formula]
  have h4 : nativeHeatPasses nativeGap138Old nativeHeat137Frames nativeHeat137Coef nativeHeat137Fixed nativeHeat137Base 4 nativeHeat137Y00 = nativeHeat137Y04 := nativeHeat137Pass04
  have h8 : nativeHeatPasses nativeGap138Old nativeHeat137Frames nativeHeat137Coef nativeHeat137Fixed nativeHeat137Base 8 nativeHeat137Y00 = nativeHeat137Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat137Pass08]
  have h12 : nativeHeatPasses nativeGap138Old nativeHeat137Frames nativeHeat137Coef nativeHeat137Fixed nativeHeat137Base 12 nativeHeat137Y00 = nativeHeat137Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat137Pass12]
  have h16 : nativeHeatPasses nativeGap138Old nativeHeat137Frames nativeHeat137Coef nativeHeat137Fixed nativeHeat137Base 16 nativeHeat137Y00 = nativeHeat137Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat137Pass16]
  have h20 : nativeHeatPasses nativeGap138Old nativeHeat137Frames nativeHeat137Coef nativeHeat137Fixed nativeHeat137Base 20 nativeHeat137Y00 = nativeHeat137Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat137Pass20]
  have h24 : nativeHeatPasses nativeGap138Old nativeHeat137Frames nativeHeat137Coef nativeHeat137Fixed nativeHeat137Base 24 nativeHeat137Y00 = nativeHeat137Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat137Pass24]
  have h28 : nativeHeatPasses nativeGap138Old nativeHeat137Frames nativeHeat137Coef nativeHeat137Fixed nativeHeat137Base 28 nativeHeat137Y00 = nativeHeat137Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat137Pass28]
  have h32 : nativeHeatPasses nativeGap138Old nativeHeat137Frames nativeHeat137Coef nativeHeat137Fixed nativeHeat137Base 32 nativeHeat137Y00 = nativeHeat137Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat137Pass32]
  have h36 : nativeHeatPasses nativeGap138Old nativeHeat137Frames nativeHeat137Coef nativeHeat137Fixed nativeHeat137Base 36 nativeHeat137Y00 = nativeHeat137Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat137Pass36]
  have h40 : nativeHeatPasses nativeGap138Old nativeHeat137Frames nativeHeat137Coef nativeHeat137Fixed nativeHeat137Base 40 nativeHeat137Y00 = nativeHeat137Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat137Pass40]
  have h44 : nativeHeatPasses nativeGap138Old nativeHeat137Frames nativeHeat137Coef nativeHeat137Fixed nativeHeat137Base 44 nativeHeat137Y00 = nativeHeat137Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat137Pass44]
  have h48 : nativeHeatPasses nativeGap138Old nativeHeat137Frames nativeHeat137Coef nativeHeat137Fixed nativeHeat137Base 48 nativeHeat137Y00 = nativeHeat137Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat137Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
