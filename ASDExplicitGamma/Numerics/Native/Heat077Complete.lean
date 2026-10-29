module
public import ASDExplicitGamma.Numerics.Native.Heat077Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat077Y00_formula : nativeHeat077Y00 = nativeHeat077Frames.y := by
  decide +kernel

theorem nativeHeat077All48 : nativeHeatPasses nativeGap078Old nativeHeat077Frames nativeHeat077Coef nativeHeat077Fixed nativeHeat077Base 48 nativeHeat077Frames.y = nativeHeat077Y48 := by
  rw [← nativeHeat077Y00_formula]
  have h4 : nativeHeatPasses nativeGap078Old nativeHeat077Frames nativeHeat077Coef nativeHeat077Fixed nativeHeat077Base 4 nativeHeat077Y00 = nativeHeat077Y04 := nativeHeat077Pass04
  have h8 : nativeHeatPasses nativeGap078Old nativeHeat077Frames nativeHeat077Coef nativeHeat077Fixed nativeHeat077Base 8 nativeHeat077Y00 = nativeHeat077Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat077Pass08]
  have h12 : nativeHeatPasses nativeGap078Old nativeHeat077Frames nativeHeat077Coef nativeHeat077Fixed nativeHeat077Base 12 nativeHeat077Y00 = nativeHeat077Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat077Pass12]
  have h16 : nativeHeatPasses nativeGap078Old nativeHeat077Frames nativeHeat077Coef nativeHeat077Fixed nativeHeat077Base 16 nativeHeat077Y00 = nativeHeat077Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat077Pass16]
  have h20 : nativeHeatPasses nativeGap078Old nativeHeat077Frames nativeHeat077Coef nativeHeat077Fixed nativeHeat077Base 20 nativeHeat077Y00 = nativeHeat077Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat077Pass20]
  have h24 : nativeHeatPasses nativeGap078Old nativeHeat077Frames nativeHeat077Coef nativeHeat077Fixed nativeHeat077Base 24 nativeHeat077Y00 = nativeHeat077Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat077Pass24]
  have h28 : nativeHeatPasses nativeGap078Old nativeHeat077Frames nativeHeat077Coef nativeHeat077Fixed nativeHeat077Base 28 nativeHeat077Y00 = nativeHeat077Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat077Pass28]
  have h32 : nativeHeatPasses nativeGap078Old nativeHeat077Frames nativeHeat077Coef nativeHeat077Fixed nativeHeat077Base 32 nativeHeat077Y00 = nativeHeat077Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat077Pass32]
  have h36 : nativeHeatPasses nativeGap078Old nativeHeat077Frames nativeHeat077Coef nativeHeat077Fixed nativeHeat077Base 36 nativeHeat077Y00 = nativeHeat077Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat077Pass36]
  have h40 : nativeHeatPasses nativeGap078Old nativeHeat077Frames nativeHeat077Coef nativeHeat077Fixed nativeHeat077Base 40 nativeHeat077Y00 = nativeHeat077Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat077Pass40]
  have h44 : nativeHeatPasses nativeGap078Old nativeHeat077Frames nativeHeat077Coef nativeHeat077Fixed nativeHeat077Base 44 nativeHeat077Y00 = nativeHeat077Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat077Pass44]
  have h48 : nativeHeatPasses nativeGap078Old nativeHeat077Frames nativeHeat077Coef nativeHeat077Fixed nativeHeat077Base 48 nativeHeat077Y00 = nativeHeat077Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat077Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
