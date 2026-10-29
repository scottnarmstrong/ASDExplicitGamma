module
public import ASDExplicitGamma.Numerics.Native.Heat043Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat043Y00_formula : nativeHeat043Y00 = nativeHeat043Frames.y := by
  decide +kernel

theorem nativeHeat043All48 : nativeHeatPasses nativeGap044Old nativeHeat043Frames nativeHeat043Coef nativeHeat043Fixed nativeHeat043Base 48 nativeHeat043Frames.y = nativeHeat043Y48 := by
  rw [← nativeHeat043Y00_formula]
  have h4 : nativeHeatPasses nativeGap044Old nativeHeat043Frames nativeHeat043Coef nativeHeat043Fixed nativeHeat043Base 4 nativeHeat043Y00 = nativeHeat043Y04 := nativeHeat043Pass04
  have h8 : nativeHeatPasses nativeGap044Old nativeHeat043Frames nativeHeat043Coef nativeHeat043Fixed nativeHeat043Base 8 nativeHeat043Y00 = nativeHeat043Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat043Pass08]
  have h12 : nativeHeatPasses nativeGap044Old nativeHeat043Frames nativeHeat043Coef nativeHeat043Fixed nativeHeat043Base 12 nativeHeat043Y00 = nativeHeat043Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat043Pass12]
  have h16 : nativeHeatPasses nativeGap044Old nativeHeat043Frames nativeHeat043Coef nativeHeat043Fixed nativeHeat043Base 16 nativeHeat043Y00 = nativeHeat043Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat043Pass16]
  have h20 : nativeHeatPasses nativeGap044Old nativeHeat043Frames nativeHeat043Coef nativeHeat043Fixed nativeHeat043Base 20 nativeHeat043Y00 = nativeHeat043Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat043Pass20]
  have h24 : nativeHeatPasses nativeGap044Old nativeHeat043Frames nativeHeat043Coef nativeHeat043Fixed nativeHeat043Base 24 nativeHeat043Y00 = nativeHeat043Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat043Pass24]
  have h28 : nativeHeatPasses nativeGap044Old nativeHeat043Frames nativeHeat043Coef nativeHeat043Fixed nativeHeat043Base 28 nativeHeat043Y00 = nativeHeat043Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat043Pass28]
  have h32 : nativeHeatPasses nativeGap044Old nativeHeat043Frames nativeHeat043Coef nativeHeat043Fixed nativeHeat043Base 32 nativeHeat043Y00 = nativeHeat043Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat043Pass32]
  have h36 : nativeHeatPasses nativeGap044Old nativeHeat043Frames nativeHeat043Coef nativeHeat043Fixed nativeHeat043Base 36 nativeHeat043Y00 = nativeHeat043Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat043Pass36]
  have h40 : nativeHeatPasses nativeGap044Old nativeHeat043Frames nativeHeat043Coef nativeHeat043Fixed nativeHeat043Base 40 nativeHeat043Y00 = nativeHeat043Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat043Pass40]
  have h44 : nativeHeatPasses nativeGap044Old nativeHeat043Frames nativeHeat043Coef nativeHeat043Fixed nativeHeat043Base 44 nativeHeat043Y00 = nativeHeat043Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat043Pass44]
  have h48 : nativeHeatPasses nativeGap044Old nativeHeat043Frames nativeHeat043Coef nativeHeat043Fixed nativeHeat043Base 48 nativeHeat043Y00 = nativeHeat043Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat043Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
