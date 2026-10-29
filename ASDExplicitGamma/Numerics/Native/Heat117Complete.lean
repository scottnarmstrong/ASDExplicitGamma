module
public import ASDExplicitGamma.Numerics.Native.Heat117Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat117Y00_formula : nativeHeat117Y00 = nativeHeat117Frames.y := by
  decide +kernel

theorem nativeHeat117All48 : nativeHeatPasses nativeGap118Old nativeHeat117Frames nativeHeat117Coef nativeHeat117Fixed nativeHeat117Base 48 nativeHeat117Frames.y = nativeHeat117Y48 := by
  rw [← nativeHeat117Y00_formula]
  have h4 : nativeHeatPasses nativeGap118Old nativeHeat117Frames nativeHeat117Coef nativeHeat117Fixed nativeHeat117Base 4 nativeHeat117Y00 = nativeHeat117Y04 := nativeHeat117Pass04
  have h8 : nativeHeatPasses nativeGap118Old nativeHeat117Frames nativeHeat117Coef nativeHeat117Fixed nativeHeat117Base 8 nativeHeat117Y00 = nativeHeat117Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat117Pass08]
  have h12 : nativeHeatPasses nativeGap118Old nativeHeat117Frames nativeHeat117Coef nativeHeat117Fixed nativeHeat117Base 12 nativeHeat117Y00 = nativeHeat117Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat117Pass12]
  have h16 : nativeHeatPasses nativeGap118Old nativeHeat117Frames nativeHeat117Coef nativeHeat117Fixed nativeHeat117Base 16 nativeHeat117Y00 = nativeHeat117Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat117Pass16]
  have h20 : nativeHeatPasses nativeGap118Old nativeHeat117Frames nativeHeat117Coef nativeHeat117Fixed nativeHeat117Base 20 nativeHeat117Y00 = nativeHeat117Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat117Pass20]
  have h24 : nativeHeatPasses nativeGap118Old nativeHeat117Frames nativeHeat117Coef nativeHeat117Fixed nativeHeat117Base 24 nativeHeat117Y00 = nativeHeat117Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat117Pass24]
  have h28 : nativeHeatPasses nativeGap118Old nativeHeat117Frames nativeHeat117Coef nativeHeat117Fixed nativeHeat117Base 28 nativeHeat117Y00 = nativeHeat117Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat117Pass28]
  have h32 : nativeHeatPasses nativeGap118Old nativeHeat117Frames nativeHeat117Coef nativeHeat117Fixed nativeHeat117Base 32 nativeHeat117Y00 = nativeHeat117Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat117Pass32]
  have h36 : nativeHeatPasses nativeGap118Old nativeHeat117Frames nativeHeat117Coef nativeHeat117Fixed nativeHeat117Base 36 nativeHeat117Y00 = nativeHeat117Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat117Pass36]
  have h40 : nativeHeatPasses nativeGap118Old nativeHeat117Frames nativeHeat117Coef nativeHeat117Fixed nativeHeat117Base 40 nativeHeat117Y00 = nativeHeat117Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat117Pass40]
  have h44 : nativeHeatPasses nativeGap118Old nativeHeat117Frames nativeHeat117Coef nativeHeat117Fixed nativeHeat117Base 44 nativeHeat117Y00 = nativeHeat117Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat117Pass44]
  have h48 : nativeHeatPasses nativeGap118Old nativeHeat117Frames nativeHeat117Coef nativeHeat117Fixed nativeHeat117Base 48 nativeHeat117Y00 = nativeHeat117Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat117Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
