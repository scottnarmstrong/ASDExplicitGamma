module
public import ASDExplicitGamma.Numerics.Native.Heat034Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat034Y00_formula : nativeHeat034Y00 = nativeHeat034Frames.y := by
  decide +kernel

theorem nativeHeat034All48 : nativeHeatPasses nativeGap035Old nativeHeat034Frames nativeHeat034Coef nativeHeat034Fixed nativeHeat034Base 48 nativeHeat034Frames.y = nativeHeat034Y48 := by
  rw [← nativeHeat034Y00_formula]
  have h4 : nativeHeatPasses nativeGap035Old nativeHeat034Frames nativeHeat034Coef nativeHeat034Fixed nativeHeat034Base 4 nativeHeat034Y00 = nativeHeat034Y04 := nativeHeat034Pass04
  have h8 : nativeHeatPasses nativeGap035Old nativeHeat034Frames nativeHeat034Coef nativeHeat034Fixed nativeHeat034Base 8 nativeHeat034Y00 = nativeHeat034Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat034Pass08]
  have h12 : nativeHeatPasses nativeGap035Old nativeHeat034Frames nativeHeat034Coef nativeHeat034Fixed nativeHeat034Base 12 nativeHeat034Y00 = nativeHeat034Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat034Pass12]
  have h16 : nativeHeatPasses nativeGap035Old nativeHeat034Frames nativeHeat034Coef nativeHeat034Fixed nativeHeat034Base 16 nativeHeat034Y00 = nativeHeat034Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat034Pass16]
  have h20 : nativeHeatPasses nativeGap035Old nativeHeat034Frames nativeHeat034Coef nativeHeat034Fixed nativeHeat034Base 20 nativeHeat034Y00 = nativeHeat034Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat034Pass20]
  have h24 : nativeHeatPasses nativeGap035Old nativeHeat034Frames nativeHeat034Coef nativeHeat034Fixed nativeHeat034Base 24 nativeHeat034Y00 = nativeHeat034Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat034Pass24]
  have h28 : nativeHeatPasses nativeGap035Old nativeHeat034Frames nativeHeat034Coef nativeHeat034Fixed nativeHeat034Base 28 nativeHeat034Y00 = nativeHeat034Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat034Pass28]
  have h32 : nativeHeatPasses nativeGap035Old nativeHeat034Frames nativeHeat034Coef nativeHeat034Fixed nativeHeat034Base 32 nativeHeat034Y00 = nativeHeat034Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat034Pass32]
  have h36 : nativeHeatPasses nativeGap035Old nativeHeat034Frames nativeHeat034Coef nativeHeat034Fixed nativeHeat034Base 36 nativeHeat034Y00 = nativeHeat034Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat034Pass36]
  have h40 : nativeHeatPasses nativeGap035Old nativeHeat034Frames nativeHeat034Coef nativeHeat034Fixed nativeHeat034Base 40 nativeHeat034Y00 = nativeHeat034Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat034Pass40]
  have h44 : nativeHeatPasses nativeGap035Old nativeHeat034Frames nativeHeat034Coef nativeHeat034Fixed nativeHeat034Base 44 nativeHeat034Y00 = nativeHeat034Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat034Pass44]
  have h48 : nativeHeatPasses nativeGap035Old nativeHeat034Frames nativeHeat034Coef nativeHeat034Fixed nativeHeat034Base 48 nativeHeat034Y00 = nativeHeat034Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat034Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
