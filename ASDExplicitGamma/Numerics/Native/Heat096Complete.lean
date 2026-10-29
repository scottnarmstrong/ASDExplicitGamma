module
public import ASDExplicitGamma.Numerics.Native.Heat096Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat096Y00_formula : nativeHeat096Y00 = nativeHeat096Frames.y := by
  decide +kernel

theorem nativeHeat096All48 : nativeHeatPasses nativeGap097Old nativeHeat096Frames nativeHeat096Coef nativeHeat096Fixed nativeHeat096Base 48 nativeHeat096Frames.y = nativeHeat096Y48 := by
  rw [← nativeHeat096Y00_formula]
  have h4 : nativeHeatPasses nativeGap097Old nativeHeat096Frames nativeHeat096Coef nativeHeat096Fixed nativeHeat096Base 4 nativeHeat096Y00 = nativeHeat096Y04 := nativeHeat096Pass04
  have h8 : nativeHeatPasses nativeGap097Old nativeHeat096Frames nativeHeat096Coef nativeHeat096Fixed nativeHeat096Base 8 nativeHeat096Y00 = nativeHeat096Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat096Pass08]
  have h12 : nativeHeatPasses nativeGap097Old nativeHeat096Frames nativeHeat096Coef nativeHeat096Fixed nativeHeat096Base 12 nativeHeat096Y00 = nativeHeat096Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat096Pass12]
  have h16 : nativeHeatPasses nativeGap097Old nativeHeat096Frames nativeHeat096Coef nativeHeat096Fixed nativeHeat096Base 16 nativeHeat096Y00 = nativeHeat096Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat096Pass16]
  have h20 : nativeHeatPasses nativeGap097Old nativeHeat096Frames nativeHeat096Coef nativeHeat096Fixed nativeHeat096Base 20 nativeHeat096Y00 = nativeHeat096Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat096Pass20]
  have h24 : nativeHeatPasses nativeGap097Old nativeHeat096Frames nativeHeat096Coef nativeHeat096Fixed nativeHeat096Base 24 nativeHeat096Y00 = nativeHeat096Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat096Pass24]
  have h28 : nativeHeatPasses nativeGap097Old nativeHeat096Frames nativeHeat096Coef nativeHeat096Fixed nativeHeat096Base 28 nativeHeat096Y00 = nativeHeat096Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat096Pass28]
  have h32 : nativeHeatPasses nativeGap097Old nativeHeat096Frames nativeHeat096Coef nativeHeat096Fixed nativeHeat096Base 32 nativeHeat096Y00 = nativeHeat096Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat096Pass32]
  have h36 : nativeHeatPasses nativeGap097Old nativeHeat096Frames nativeHeat096Coef nativeHeat096Fixed nativeHeat096Base 36 nativeHeat096Y00 = nativeHeat096Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat096Pass36]
  have h40 : nativeHeatPasses nativeGap097Old nativeHeat096Frames nativeHeat096Coef nativeHeat096Fixed nativeHeat096Base 40 nativeHeat096Y00 = nativeHeat096Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat096Pass40]
  have h44 : nativeHeatPasses nativeGap097Old nativeHeat096Frames nativeHeat096Coef nativeHeat096Fixed nativeHeat096Base 44 nativeHeat096Y00 = nativeHeat096Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat096Pass44]
  have h48 : nativeHeatPasses nativeGap097Old nativeHeat096Frames nativeHeat096Coef nativeHeat096Fixed nativeHeat096Base 48 nativeHeat096Y00 = nativeHeat096Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat096Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
