module
public import ASDExplicitGamma.Numerics.Native.Heat149Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat149Y00_formula : nativeHeat149Y00 = nativeHeat149Frames.y := by
  decide +kernel

theorem nativeHeat149All48 : nativeHeatPasses nativeGap150Old nativeHeat149Frames nativeHeat149Coef nativeHeat149Fixed nativeHeat149Base 48 nativeHeat149Frames.y = nativeHeat149Y48 := by
  rw [← nativeHeat149Y00_formula]
  have h4 : nativeHeatPasses nativeGap150Old nativeHeat149Frames nativeHeat149Coef nativeHeat149Fixed nativeHeat149Base 4 nativeHeat149Y00 = nativeHeat149Y04 := nativeHeat149Pass04
  have h8 : nativeHeatPasses nativeGap150Old nativeHeat149Frames nativeHeat149Coef nativeHeat149Fixed nativeHeat149Base 8 nativeHeat149Y00 = nativeHeat149Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat149Pass08]
  have h12 : nativeHeatPasses nativeGap150Old nativeHeat149Frames nativeHeat149Coef nativeHeat149Fixed nativeHeat149Base 12 nativeHeat149Y00 = nativeHeat149Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat149Pass12]
  have h16 : nativeHeatPasses nativeGap150Old nativeHeat149Frames nativeHeat149Coef nativeHeat149Fixed nativeHeat149Base 16 nativeHeat149Y00 = nativeHeat149Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat149Pass16]
  have h20 : nativeHeatPasses nativeGap150Old nativeHeat149Frames nativeHeat149Coef nativeHeat149Fixed nativeHeat149Base 20 nativeHeat149Y00 = nativeHeat149Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat149Pass20]
  have h24 : nativeHeatPasses nativeGap150Old nativeHeat149Frames nativeHeat149Coef nativeHeat149Fixed nativeHeat149Base 24 nativeHeat149Y00 = nativeHeat149Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat149Pass24]
  have h28 : nativeHeatPasses nativeGap150Old nativeHeat149Frames nativeHeat149Coef nativeHeat149Fixed nativeHeat149Base 28 nativeHeat149Y00 = nativeHeat149Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat149Pass28]
  have h32 : nativeHeatPasses nativeGap150Old nativeHeat149Frames nativeHeat149Coef nativeHeat149Fixed nativeHeat149Base 32 nativeHeat149Y00 = nativeHeat149Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat149Pass32]
  have h36 : nativeHeatPasses nativeGap150Old nativeHeat149Frames nativeHeat149Coef nativeHeat149Fixed nativeHeat149Base 36 nativeHeat149Y00 = nativeHeat149Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat149Pass36]
  have h40 : nativeHeatPasses nativeGap150Old nativeHeat149Frames nativeHeat149Coef nativeHeat149Fixed nativeHeat149Base 40 nativeHeat149Y00 = nativeHeat149Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat149Pass40]
  have h44 : nativeHeatPasses nativeGap150Old nativeHeat149Frames nativeHeat149Coef nativeHeat149Fixed nativeHeat149Base 44 nativeHeat149Y00 = nativeHeat149Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat149Pass44]
  have h48 : nativeHeatPasses nativeGap150Old nativeHeat149Frames nativeHeat149Coef nativeHeat149Fixed nativeHeat149Base 48 nativeHeat149Y00 = nativeHeat149Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat149Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
