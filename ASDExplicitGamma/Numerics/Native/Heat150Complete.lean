module
public import ASDExplicitGamma.Numerics.Native.Heat150Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat150Y00_formula : nativeHeat150Y00 = nativeHeat150Frames.y := by
  decide +kernel

theorem nativeHeat150All48 : nativeHeatPasses nativeGap151Old nativeHeat150Frames nativeHeat150Coef nativeHeat150Fixed nativeHeat150Base 48 nativeHeat150Frames.y = nativeHeat150Y48 := by
  rw [← nativeHeat150Y00_formula]
  have h4 : nativeHeatPasses nativeGap151Old nativeHeat150Frames nativeHeat150Coef nativeHeat150Fixed nativeHeat150Base 4 nativeHeat150Y00 = nativeHeat150Y04 := nativeHeat150Pass04
  have h8 : nativeHeatPasses nativeGap151Old nativeHeat150Frames nativeHeat150Coef nativeHeat150Fixed nativeHeat150Base 8 nativeHeat150Y00 = nativeHeat150Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat150Pass08]
  have h12 : nativeHeatPasses nativeGap151Old nativeHeat150Frames nativeHeat150Coef nativeHeat150Fixed nativeHeat150Base 12 nativeHeat150Y00 = nativeHeat150Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat150Pass12]
  have h16 : nativeHeatPasses nativeGap151Old nativeHeat150Frames nativeHeat150Coef nativeHeat150Fixed nativeHeat150Base 16 nativeHeat150Y00 = nativeHeat150Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat150Pass16]
  have h20 : nativeHeatPasses nativeGap151Old nativeHeat150Frames nativeHeat150Coef nativeHeat150Fixed nativeHeat150Base 20 nativeHeat150Y00 = nativeHeat150Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat150Pass20]
  have h24 : nativeHeatPasses nativeGap151Old nativeHeat150Frames nativeHeat150Coef nativeHeat150Fixed nativeHeat150Base 24 nativeHeat150Y00 = nativeHeat150Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat150Pass24]
  have h28 : nativeHeatPasses nativeGap151Old nativeHeat150Frames nativeHeat150Coef nativeHeat150Fixed nativeHeat150Base 28 nativeHeat150Y00 = nativeHeat150Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat150Pass28]
  have h32 : nativeHeatPasses nativeGap151Old nativeHeat150Frames nativeHeat150Coef nativeHeat150Fixed nativeHeat150Base 32 nativeHeat150Y00 = nativeHeat150Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat150Pass32]
  have h36 : nativeHeatPasses nativeGap151Old nativeHeat150Frames nativeHeat150Coef nativeHeat150Fixed nativeHeat150Base 36 nativeHeat150Y00 = nativeHeat150Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat150Pass36]
  have h40 : nativeHeatPasses nativeGap151Old nativeHeat150Frames nativeHeat150Coef nativeHeat150Fixed nativeHeat150Base 40 nativeHeat150Y00 = nativeHeat150Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat150Pass40]
  have h44 : nativeHeatPasses nativeGap151Old nativeHeat150Frames nativeHeat150Coef nativeHeat150Fixed nativeHeat150Base 44 nativeHeat150Y00 = nativeHeat150Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat150Pass44]
  have h48 : nativeHeatPasses nativeGap151Old nativeHeat150Frames nativeHeat150Coef nativeHeat150Fixed nativeHeat150Base 48 nativeHeat150Y00 = nativeHeat150Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat150Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
