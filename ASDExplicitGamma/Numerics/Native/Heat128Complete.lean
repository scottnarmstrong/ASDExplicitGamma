module
public import ASDExplicitGamma.Numerics.Native.Heat128Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat128Y00_formula : nativeHeat128Y00 = nativeHeat128Frames.y := by
  decide +kernel

theorem nativeHeat128All48 : nativeHeatPasses nativeGap129Old nativeHeat128Frames nativeHeat128Coef nativeHeat128Fixed nativeHeat128Base 48 nativeHeat128Frames.y = nativeHeat128Y48 := by
  rw [← nativeHeat128Y00_formula]
  have h4 : nativeHeatPasses nativeGap129Old nativeHeat128Frames nativeHeat128Coef nativeHeat128Fixed nativeHeat128Base 4 nativeHeat128Y00 = nativeHeat128Y04 := nativeHeat128Pass04
  have h8 : nativeHeatPasses nativeGap129Old nativeHeat128Frames nativeHeat128Coef nativeHeat128Fixed nativeHeat128Base 8 nativeHeat128Y00 = nativeHeat128Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat128Pass08]
  have h12 : nativeHeatPasses nativeGap129Old nativeHeat128Frames nativeHeat128Coef nativeHeat128Fixed nativeHeat128Base 12 nativeHeat128Y00 = nativeHeat128Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat128Pass12]
  have h16 : nativeHeatPasses nativeGap129Old nativeHeat128Frames nativeHeat128Coef nativeHeat128Fixed nativeHeat128Base 16 nativeHeat128Y00 = nativeHeat128Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat128Pass16]
  have h20 : nativeHeatPasses nativeGap129Old nativeHeat128Frames nativeHeat128Coef nativeHeat128Fixed nativeHeat128Base 20 nativeHeat128Y00 = nativeHeat128Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat128Pass20]
  have h24 : nativeHeatPasses nativeGap129Old nativeHeat128Frames nativeHeat128Coef nativeHeat128Fixed nativeHeat128Base 24 nativeHeat128Y00 = nativeHeat128Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat128Pass24]
  have h28 : nativeHeatPasses nativeGap129Old nativeHeat128Frames nativeHeat128Coef nativeHeat128Fixed nativeHeat128Base 28 nativeHeat128Y00 = nativeHeat128Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat128Pass28]
  have h32 : nativeHeatPasses nativeGap129Old nativeHeat128Frames nativeHeat128Coef nativeHeat128Fixed nativeHeat128Base 32 nativeHeat128Y00 = nativeHeat128Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat128Pass32]
  have h36 : nativeHeatPasses nativeGap129Old nativeHeat128Frames nativeHeat128Coef nativeHeat128Fixed nativeHeat128Base 36 nativeHeat128Y00 = nativeHeat128Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat128Pass36]
  have h40 : nativeHeatPasses nativeGap129Old nativeHeat128Frames nativeHeat128Coef nativeHeat128Fixed nativeHeat128Base 40 nativeHeat128Y00 = nativeHeat128Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat128Pass40]
  have h44 : nativeHeatPasses nativeGap129Old nativeHeat128Frames nativeHeat128Coef nativeHeat128Fixed nativeHeat128Base 44 nativeHeat128Y00 = nativeHeat128Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat128Pass44]
  have h48 : nativeHeatPasses nativeGap129Old nativeHeat128Frames nativeHeat128Coef nativeHeat128Fixed nativeHeat128Base 48 nativeHeat128Y00 = nativeHeat128Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat128Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
