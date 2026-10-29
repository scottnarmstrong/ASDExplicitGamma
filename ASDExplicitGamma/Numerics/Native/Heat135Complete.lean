module
public import ASDExplicitGamma.Numerics.Native.Heat135Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat135Y00_formula : nativeHeat135Y00 = nativeHeat135Frames.y := by
  decide +kernel

theorem nativeHeat135All48 : nativeHeatPasses nativeGap136Old nativeHeat135Frames nativeHeat135Coef nativeHeat135Fixed nativeHeat135Base 48 nativeHeat135Frames.y = nativeHeat135Y48 := by
  rw [← nativeHeat135Y00_formula]
  have h4 : nativeHeatPasses nativeGap136Old nativeHeat135Frames nativeHeat135Coef nativeHeat135Fixed nativeHeat135Base 4 nativeHeat135Y00 = nativeHeat135Y04 := nativeHeat135Pass04
  have h8 : nativeHeatPasses nativeGap136Old nativeHeat135Frames nativeHeat135Coef nativeHeat135Fixed nativeHeat135Base 8 nativeHeat135Y00 = nativeHeat135Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat135Pass08]
  have h12 : nativeHeatPasses nativeGap136Old nativeHeat135Frames nativeHeat135Coef nativeHeat135Fixed nativeHeat135Base 12 nativeHeat135Y00 = nativeHeat135Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat135Pass12]
  have h16 : nativeHeatPasses nativeGap136Old nativeHeat135Frames nativeHeat135Coef nativeHeat135Fixed nativeHeat135Base 16 nativeHeat135Y00 = nativeHeat135Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat135Pass16]
  have h20 : nativeHeatPasses nativeGap136Old nativeHeat135Frames nativeHeat135Coef nativeHeat135Fixed nativeHeat135Base 20 nativeHeat135Y00 = nativeHeat135Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat135Pass20]
  have h24 : nativeHeatPasses nativeGap136Old nativeHeat135Frames nativeHeat135Coef nativeHeat135Fixed nativeHeat135Base 24 nativeHeat135Y00 = nativeHeat135Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat135Pass24]
  have h28 : nativeHeatPasses nativeGap136Old nativeHeat135Frames nativeHeat135Coef nativeHeat135Fixed nativeHeat135Base 28 nativeHeat135Y00 = nativeHeat135Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat135Pass28]
  have h32 : nativeHeatPasses nativeGap136Old nativeHeat135Frames nativeHeat135Coef nativeHeat135Fixed nativeHeat135Base 32 nativeHeat135Y00 = nativeHeat135Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat135Pass32]
  have h36 : nativeHeatPasses nativeGap136Old nativeHeat135Frames nativeHeat135Coef nativeHeat135Fixed nativeHeat135Base 36 nativeHeat135Y00 = nativeHeat135Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat135Pass36]
  have h40 : nativeHeatPasses nativeGap136Old nativeHeat135Frames nativeHeat135Coef nativeHeat135Fixed nativeHeat135Base 40 nativeHeat135Y00 = nativeHeat135Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat135Pass40]
  have h44 : nativeHeatPasses nativeGap136Old nativeHeat135Frames nativeHeat135Coef nativeHeat135Fixed nativeHeat135Base 44 nativeHeat135Y00 = nativeHeat135Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat135Pass44]
  have h48 : nativeHeatPasses nativeGap136Old nativeHeat135Frames nativeHeat135Coef nativeHeat135Fixed nativeHeat135Base 48 nativeHeat135Y00 = nativeHeat135Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat135Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
