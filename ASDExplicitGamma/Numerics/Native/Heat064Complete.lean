module
public import ASDExplicitGamma.Numerics.Native.Heat064Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat064Y00_formula : nativeHeat064Y00 = nativeHeat064Frames.y := by
  decide +kernel

theorem nativeHeat064All48 : nativeHeatPasses nativeGap065Old nativeHeat064Frames nativeHeat064Coef nativeHeat064Fixed nativeHeat064Base 48 nativeHeat064Frames.y = nativeHeat064Y48 := by
  rw [← nativeHeat064Y00_formula]
  have h4 : nativeHeatPasses nativeGap065Old nativeHeat064Frames nativeHeat064Coef nativeHeat064Fixed nativeHeat064Base 4 nativeHeat064Y00 = nativeHeat064Y04 := nativeHeat064Pass04
  have h8 : nativeHeatPasses nativeGap065Old nativeHeat064Frames nativeHeat064Coef nativeHeat064Fixed nativeHeat064Base 8 nativeHeat064Y00 = nativeHeat064Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat064Pass08]
  have h12 : nativeHeatPasses nativeGap065Old nativeHeat064Frames nativeHeat064Coef nativeHeat064Fixed nativeHeat064Base 12 nativeHeat064Y00 = nativeHeat064Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat064Pass12]
  have h16 : nativeHeatPasses nativeGap065Old nativeHeat064Frames nativeHeat064Coef nativeHeat064Fixed nativeHeat064Base 16 nativeHeat064Y00 = nativeHeat064Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat064Pass16]
  have h20 : nativeHeatPasses nativeGap065Old nativeHeat064Frames nativeHeat064Coef nativeHeat064Fixed nativeHeat064Base 20 nativeHeat064Y00 = nativeHeat064Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat064Pass20]
  have h24 : nativeHeatPasses nativeGap065Old nativeHeat064Frames nativeHeat064Coef nativeHeat064Fixed nativeHeat064Base 24 nativeHeat064Y00 = nativeHeat064Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat064Pass24]
  have h28 : nativeHeatPasses nativeGap065Old nativeHeat064Frames nativeHeat064Coef nativeHeat064Fixed nativeHeat064Base 28 nativeHeat064Y00 = nativeHeat064Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat064Pass28]
  have h32 : nativeHeatPasses nativeGap065Old nativeHeat064Frames nativeHeat064Coef nativeHeat064Fixed nativeHeat064Base 32 nativeHeat064Y00 = nativeHeat064Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat064Pass32]
  have h36 : nativeHeatPasses nativeGap065Old nativeHeat064Frames nativeHeat064Coef nativeHeat064Fixed nativeHeat064Base 36 nativeHeat064Y00 = nativeHeat064Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat064Pass36]
  have h40 : nativeHeatPasses nativeGap065Old nativeHeat064Frames nativeHeat064Coef nativeHeat064Fixed nativeHeat064Base 40 nativeHeat064Y00 = nativeHeat064Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat064Pass40]
  have h44 : nativeHeatPasses nativeGap065Old nativeHeat064Frames nativeHeat064Coef nativeHeat064Fixed nativeHeat064Base 44 nativeHeat064Y00 = nativeHeat064Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat064Pass44]
  have h48 : nativeHeatPasses nativeGap065Old nativeHeat064Frames nativeHeat064Coef nativeHeat064Fixed nativeHeat064Base 48 nativeHeat064Y00 = nativeHeat064Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat064Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
