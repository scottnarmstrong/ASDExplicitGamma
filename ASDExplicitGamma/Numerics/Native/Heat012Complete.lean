module
public import ASDExplicitGamma.Numerics.Native.Heat012Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat012Y00_formula : nativeHeat012Y00 = nativeHeat012Frames.y := by
  decide +kernel

theorem nativeHeat012All48 : nativeHeatPasses nativeGap013Old nativeHeat012Frames nativeHeat012Coef nativeHeat012Fixed nativeHeat012Base 48 nativeHeat012Frames.y = nativeHeat012Y48 := by
  rw [← nativeHeat012Y00_formula]
  have h4 : nativeHeatPasses nativeGap013Old nativeHeat012Frames nativeHeat012Coef nativeHeat012Fixed nativeHeat012Base 4 nativeHeat012Y00 = nativeHeat012Y04 := nativeHeat012Pass04
  have h8 : nativeHeatPasses nativeGap013Old nativeHeat012Frames nativeHeat012Coef nativeHeat012Fixed nativeHeat012Base 8 nativeHeat012Y00 = nativeHeat012Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat012Pass08]
  have h12 : nativeHeatPasses nativeGap013Old nativeHeat012Frames nativeHeat012Coef nativeHeat012Fixed nativeHeat012Base 12 nativeHeat012Y00 = nativeHeat012Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat012Pass12]
  have h16 : nativeHeatPasses nativeGap013Old nativeHeat012Frames nativeHeat012Coef nativeHeat012Fixed nativeHeat012Base 16 nativeHeat012Y00 = nativeHeat012Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat012Pass16]
  have h20 : nativeHeatPasses nativeGap013Old nativeHeat012Frames nativeHeat012Coef nativeHeat012Fixed nativeHeat012Base 20 nativeHeat012Y00 = nativeHeat012Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat012Pass20]
  have h24 : nativeHeatPasses nativeGap013Old nativeHeat012Frames nativeHeat012Coef nativeHeat012Fixed nativeHeat012Base 24 nativeHeat012Y00 = nativeHeat012Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat012Pass24]
  have h28 : nativeHeatPasses nativeGap013Old nativeHeat012Frames nativeHeat012Coef nativeHeat012Fixed nativeHeat012Base 28 nativeHeat012Y00 = nativeHeat012Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat012Pass28]
  have h32 : nativeHeatPasses nativeGap013Old nativeHeat012Frames nativeHeat012Coef nativeHeat012Fixed nativeHeat012Base 32 nativeHeat012Y00 = nativeHeat012Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat012Pass32]
  have h36 : nativeHeatPasses nativeGap013Old nativeHeat012Frames nativeHeat012Coef nativeHeat012Fixed nativeHeat012Base 36 nativeHeat012Y00 = nativeHeat012Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat012Pass36]
  have h40 : nativeHeatPasses nativeGap013Old nativeHeat012Frames nativeHeat012Coef nativeHeat012Fixed nativeHeat012Base 40 nativeHeat012Y00 = nativeHeat012Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat012Pass40]
  have h44 : nativeHeatPasses nativeGap013Old nativeHeat012Frames nativeHeat012Coef nativeHeat012Fixed nativeHeat012Base 44 nativeHeat012Y00 = nativeHeat012Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat012Pass44]
  have h48 : nativeHeatPasses nativeGap013Old nativeHeat012Frames nativeHeat012Coef nativeHeat012Fixed nativeHeat012Base 48 nativeHeat012Y00 = nativeHeat012Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat012Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
