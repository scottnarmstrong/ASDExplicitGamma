module
public import ASDExplicitGamma.Numerics.Native.Heat157Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat157Y00_formula : nativeHeat157Y00 = nativeHeat157Frames.y := by
  decide +kernel

theorem nativeHeat157All48 : nativeHeatPasses nativeGap158Old nativeHeat157Frames nativeHeat157Coef nativeHeat157Fixed nativeHeat157Base 48 nativeHeat157Frames.y = nativeHeat157Y48 := by
  rw [← nativeHeat157Y00_formula]
  have h4 : nativeHeatPasses nativeGap158Old nativeHeat157Frames nativeHeat157Coef nativeHeat157Fixed nativeHeat157Base 4 nativeHeat157Y00 = nativeHeat157Y04 := nativeHeat157Pass04
  have h8 : nativeHeatPasses nativeGap158Old nativeHeat157Frames nativeHeat157Coef nativeHeat157Fixed nativeHeat157Base 8 nativeHeat157Y00 = nativeHeat157Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat157Pass08]
  have h12 : nativeHeatPasses nativeGap158Old nativeHeat157Frames nativeHeat157Coef nativeHeat157Fixed nativeHeat157Base 12 nativeHeat157Y00 = nativeHeat157Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat157Pass12]
  have h16 : nativeHeatPasses nativeGap158Old nativeHeat157Frames nativeHeat157Coef nativeHeat157Fixed nativeHeat157Base 16 nativeHeat157Y00 = nativeHeat157Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat157Pass16]
  have h20 : nativeHeatPasses nativeGap158Old nativeHeat157Frames nativeHeat157Coef nativeHeat157Fixed nativeHeat157Base 20 nativeHeat157Y00 = nativeHeat157Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat157Pass20]
  have h24 : nativeHeatPasses nativeGap158Old nativeHeat157Frames nativeHeat157Coef nativeHeat157Fixed nativeHeat157Base 24 nativeHeat157Y00 = nativeHeat157Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat157Pass24]
  have h28 : nativeHeatPasses nativeGap158Old nativeHeat157Frames nativeHeat157Coef nativeHeat157Fixed nativeHeat157Base 28 nativeHeat157Y00 = nativeHeat157Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat157Pass28]
  have h32 : nativeHeatPasses nativeGap158Old nativeHeat157Frames nativeHeat157Coef nativeHeat157Fixed nativeHeat157Base 32 nativeHeat157Y00 = nativeHeat157Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat157Pass32]
  have h36 : nativeHeatPasses nativeGap158Old nativeHeat157Frames nativeHeat157Coef nativeHeat157Fixed nativeHeat157Base 36 nativeHeat157Y00 = nativeHeat157Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat157Pass36]
  have h40 : nativeHeatPasses nativeGap158Old nativeHeat157Frames nativeHeat157Coef nativeHeat157Fixed nativeHeat157Base 40 nativeHeat157Y00 = nativeHeat157Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat157Pass40]
  have h44 : nativeHeatPasses nativeGap158Old nativeHeat157Frames nativeHeat157Coef nativeHeat157Fixed nativeHeat157Base 44 nativeHeat157Y00 = nativeHeat157Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat157Pass44]
  have h48 : nativeHeatPasses nativeGap158Old nativeHeat157Frames nativeHeat157Coef nativeHeat157Fixed nativeHeat157Base 48 nativeHeat157Y00 = nativeHeat157Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat157Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
