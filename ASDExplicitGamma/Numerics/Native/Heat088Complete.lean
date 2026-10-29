module
public import ASDExplicitGamma.Numerics.Native.Heat088Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat088Y00_formula : nativeHeat088Y00 = nativeHeat088Frames.y := by
  decide +kernel

theorem nativeHeat088All48 : nativeHeatPasses nativeGap089Old nativeHeat088Frames nativeHeat088Coef nativeHeat088Fixed nativeHeat088Base 48 nativeHeat088Frames.y = nativeHeat088Y48 := by
  rw [← nativeHeat088Y00_formula]
  have h4 : nativeHeatPasses nativeGap089Old nativeHeat088Frames nativeHeat088Coef nativeHeat088Fixed nativeHeat088Base 4 nativeHeat088Y00 = nativeHeat088Y04 := nativeHeat088Pass04
  have h8 : nativeHeatPasses nativeGap089Old nativeHeat088Frames nativeHeat088Coef nativeHeat088Fixed nativeHeat088Base 8 nativeHeat088Y00 = nativeHeat088Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat088Pass08]
  have h12 : nativeHeatPasses nativeGap089Old nativeHeat088Frames nativeHeat088Coef nativeHeat088Fixed nativeHeat088Base 12 nativeHeat088Y00 = nativeHeat088Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat088Pass12]
  have h16 : nativeHeatPasses nativeGap089Old nativeHeat088Frames nativeHeat088Coef nativeHeat088Fixed nativeHeat088Base 16 nativeHeat088Y00 = nativeHeat088Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat088Pass16]
  have h20 : nativeHeatPasses nativeGap089Old nativeHeat088Frames nativeHeat088Coef nativeHeat088Fixed nativeHeat088Base 20 nativeHeat088Y00 = nativeHeat088Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat088Pass20]
  have h24 : nativeHeatPasses nativeGap089Old nativeHeat088Frames nativeHeat088Coef nativeHeat088Fixed nativeHeat088Base 24 nativeHeat088Y00 = nativeHeat088Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat088Pass24]
  have h28 : nativeHeatPasses nativeGap089Old nativeHeat088Frames nativeHeat088Coef nativeHeat088Fixed nativeHeat088Base 28 nativeHeat088Y00 = nativeHeat088Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat088Pass28]
  have h32 : nativeHeatPasses nativeGap089Old nativeHeat088Frames nativeHeat088Coef nativeHeat088Fixed nativeHeat088Base 32 nativeHeat088Y00 = nativeHeat088Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat088Pass32]
  have h36 : nativeHeatPasses nativeGap089Old nativeHeat088Frames nativeHeat088Coef nativeHeat088Fixed nativeHeat088Base 36 nativeHeat088Y00 = nativeHeat088Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat088Pass36]
  have h40 : nativeHeatPasses nativeGap089Old nativeHeat088Frames nativeHeat088Coef nativeHeat088Fixed nativeHeat088Base 40 nativeHeat088Y00 = nativeHeat088Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat088Pass40]
  have h44 : nativeHeatPasses nativeGap089Old nativeHeat088Frames nativeHeat088Coef nativeHeat088Fixed nativeHeat088Base 44 nativeHeat088Y00 = nativeHeat088Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat088Pass44]
  have h48 : nativeHeatPasses nativeGap089Old nativeHeat088Frames nativeHeat088Coef nativeHeat088Fixed nativeHeat088Base 48 nativeHeat088Y00 = nativeHeat088Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat088Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
