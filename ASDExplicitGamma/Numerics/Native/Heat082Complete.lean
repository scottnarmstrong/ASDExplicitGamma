module
public import ASDExplicitGamma.Numerics.Native.Heat082Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat082Y00_formula : nativeHeat082Y00 = nativeHeat082Frames.y := by
  decide +kernel

theorem nativeHeat082All48 : nativeHeatPasses nativeGap083Old nativeHeat082Frames nativeHeat082Coef nativeHeat082Fixed nativeHeat082Base 48 nativeHeat082Frames.y = nativeHeat082Y48 := by
  rw [← nativeHeat082Y00_formula]
  have h4 : nativeHeatPasses nativeGap083Old nativeHeat082Frames nativeHeat082Coef nativeHeat082Fixed nativeHeat082Base 4 nativeHeat082Y00 = nativeHeat082Y04 := nativeHeat082Pass04
  have h8 : nativeHeatPasses nativeGap083Old nativeHeat082Frames nativeHeat082Coef nativeHeat082Fixed nativeHeat082Base 8 nativeHeat082Y00 = nativeHeat082Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat082Pass08]
  have h12 : nativeHeatPasses nativeGap083Old nativeHeat082Frames nativeHeat082Coef nativeHeat082Fixed nativeHeat082Base 12 nativeHeat082Y00 = nativeHeat082Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat082Pass12]
  have h16 : nativeHeatPasses nativeGap083Old nativeHeat082Frames nativeHeat082Coef nativeHeat082Fixed nativeHeat082Base 16 nativeHeat082Y00 = nativeHeat082Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat082Pass16]
  have h20 : nativeHeatPasses nativeGap083Old nativeHeat082Frames nativeHeat082Coef nativeHeat082Fixed nativeHeat082Base 20 nativeHeat082Y00 = nativeHeat082Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat082Pass20]
  have h24 : nativeHeatPasses nativeGap083Old nativeHeat082Frames nativeHeat082Coef nativeHeat082Fixed nativeHeat082Base 24 nativeHeat082Y00 = nativeHeat082Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat082Pass24]
  have h28 : nativeHeatPasses nativeGap083Old nativeHeat082Frames nativeHeat082Coef nativeHeat082Fixed nativeHeat082Base 28 nativeHeat082Y00 = nativeHeat082Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat082Pass28]
  have h32 : nativeHeatPasses nativeGap083Old nativeHeat082Frames nativeHeat082Coef nativeHeat082Fixed nativeHeat082Base 32 nativeHeat082Y00 = nativeHeat082Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat082Pass32]
  have h36 : nativeHeatPasses nativeGap083Old nativeHeat082Frames nativeHeat082Coef nativeHeat082Fixed nativeHeat082Base 36 nativeHeat082Y00 = nativeHeat082Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat082Pass36]
  have h40 : nativeHeatPasses nativeGap083Old nativeHeat082Frames nativeHeat082Coef nativeHeat082Fixed nativeHeat082Base 40 nativeHeat082Y00 = nativeHeat082Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat082Pass40]
  have h44 : nativeHeatPasses nativeGap083Old nativeHeat082Frames nativeHeat082Coef nativeHeat082Fixed nativeHeat082Base 44 nativeHeat082Y00 = nativeHeat082Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat082Pass44]
  have h48 : nativeHeatPasses nativeGap083Old nativeHeat082Frames nativeHeat082Coef nativeHeat082Fixed nativeHeat082Base 48 nativeHeat082Y00 = nativeHeat082Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat082Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
