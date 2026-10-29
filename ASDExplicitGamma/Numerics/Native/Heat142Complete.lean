module
public import ASDExplicitGamma.Numerics.Native.Heat142Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat142Y00_formula : nativeHeat142Y00 = nativeHeat142Frames.y := by
  decide +kernel

theorem nativeHeat142All48 : nativeHeatPasses nativeGap143Old nativeHeat142Frames nativeHeat142Coef nativeHeat142Fixed nativeHeat142Base 48 nativeHeat142Frames.y = nativeHeat142Y48 := by
  rw [← nativeHeat142Y00_formula]
  have h4 : nativeHeatPasses nativeGap143Old nativeHeat142Frames nativeHeat142Coef nativeHeat142Fixed nativeHeat142Base 4 nativeHeat142Y00 = nativeHeat142Y04 := nativeHeat142Pass04
  have h8 : nativeHeatPasses nativeGap143Old nativeHeat142Frames nativeHeat142Coef nativeHeat142Fixed nativeHeat142Base 8 nativeHeat142Y00 = nativeHeat142Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat142Pass08]
  have h12 : nativeHeatPasses nativeGap143Old nativeHeat142Frames nativeHeat142Coef nativeHeat142Fixed nativeHeat142Base 12 nativeHeat142Y00 = nativeHeat142Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat142Pass12]
  have h16 : nativeHeatPasses nativeGap143Old nativeHeat142Frames nativeHeat142Coef nativeHeat142Fixed nativeHeat142Base 16 nativeHeat142Y00 = nativeHeat142Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat142Pass16]
  have h20 : nativeHeatPasses nativeGap143Old nativeHeat142Frames nativeHeat142Coef nativeHeat142Fixed nativeHeat142Base 20 nativeHeat142Y00 = nativeHeat142Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat142Pass20]
  have h24 : nativeHeatPasses nativeGap143Old nativeHeat142Frames nativeHeat142Coef nativeHeat142Fixed nativeHeat142Base 24 nativeHeat142Y00 = nativeHeat142Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat142Pass24]
  have h28 : nativeHeatPasses nativeGap143Old nativeHeat142Frames nativeHeat142Coef nativeHeat142Fixed nativeHeat142Base 28 nativeHeat142Y00 = nativeHeat142Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat142Pass28]
  have h32 : nativeHeatPasses nativeGap143Old nativeHeat142Frames nativeHeat142Coef nativeHeat142Fixed nativeHeat142Base 32 nativeHeat142Y00 = nativeHeat142Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat142Pass32]
  have h36 : nativeHeatPasses nativeGap143Old nativeHeat142Frames nativeHeat142Coef nativeHeat142Fixed nativeHeat142Base 36 nativeHeat142Y00 = nativeHeat142Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat142Pass36]
  have h40 : nativeHeatPasses nativeGap143Old nativeHeat142Frames nativeHeat142Coef nativeHeat142Fixed nativeHeat142Base 40 nativeHeat142Y00 = nativeHeat142Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat142Pass40]
  have h44 : nativeHeatPasses nativeGap143Old nativeHeat142Frames nativeHeat142Coef nativeHeat142Fixed nativeHeat142Base 44 nativeHeat142Y00 = nativeHeat142Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat142Pass44]
  have h48 : nativeHeatPasses nativeGap143Old nativeHeat142Frames nativeHeat142Coef nativeHeat142Fixed nativeHeat142Base 48 nativeHeat142Y00 = nativeHeat142Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat142Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
