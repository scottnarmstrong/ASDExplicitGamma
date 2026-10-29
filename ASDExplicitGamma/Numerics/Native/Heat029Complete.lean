module
public import ASDExplicitGamma.Numerics.Native.Heat029Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat029Y00_formula : nativeHeat029Y00 = nativeHeat029Frames.y := by
  decide +kernel

theorem nativeHeat029All48 : nativeHeatPasses nativeGap030Old nativeHeat029Frames nativeHeat029Coef nativeHeat029Fixed nativeHeat029Base 48 nativeHeat029Frames.y = nativeHeat029Y48 := by
  rw [← nativeHeat029Y00_formula]
  have h4 : nativeHeatPasses nativeGap030Old nativeHeat029Frames nativeHeat029Coef nativeHeat029Fixed nativeHeat029Base 4 nativeHeat029Y00 = nativeHeat029Y04 := nativeHeat029Pass04
  have h8 : nativeHeatPasses nativeGap030Old nativeHeat029Frames nativeHeat029Coef nativeHeat029Fixed nativeHeat029Base 8 nativeHeat029Y00 = nativeHeat029Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat029Pass08]
  have h12 : nativeHeatPasses nativeGap030Old nativeHeat029Frames nativeHeat029Coef nativeHeat029Fixed nativeHeat029Base 12 nativeHeat029Y00 = nativeHeat029Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat029Pass12]
  have h16 : nativeHeatPasses nativeGap030Old nativeHeat029Frames nativeHeat029Coef nativeHeat029Fixed nativeHeat029Base 16 nativeHeat029Y00 = nativeHeat029Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat029Pass16]
  have h20 : nativeHeatPasses nativeGap030Old nativeHeat029Frames nativeHeat029Coef nativeHeat029Fixed nativeHeat029Base 20 nativeHeat029Y00 = nativeHeat029Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat029Pass20]
  have h24 : nativeHeatPasses nativeGap030Old nativeHeat029Frames nativeHeat029Coef nativeHeat029Fixed nativeHeat029Base 24 nativeHeat029Y00 = nativeHeat029Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat029Pass24]
  have h28 : nativeHeatPasses nativeGap030Old nativeHeat029Frames nativeHeat029Coef nativeHeat029Fixed nativeHeat029Base 28 nativeHeat029Y00 = nativeHeat029Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat029Pass28]
  have h32 : nativeHeatPasses nativeGap030Old nativeHeat029Frames nativeHeat029Coef nativeHeat029Fixed nativeHeat029Base 32 nativeHeat029Y00 = nativeHeat029Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat029Pass32]
  have h36 : nativeHeatPasses nativeGap030Old nativeHeat029Frames nativeHeat029Coef nativeHeat029Fixed nativeHeat029Base 36 nativeHeat029Y00 = nativeHeat029Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat029Pass36]
  have h40 : nativeHeatPasses nativeGap030Old nativeHeat029Frames nativeHeat029Coef nativeHeat029Fixed nativeHeat029Base 40 nativeHeat029Y00 = nativeHeat029Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat029Pass40]
  have h44 : nativeHeatPasses nativeGap030Old nativeHeat029Frames nativeHeat029Coef nativeHeat029Fixed nativeHeat029Base 44 nativeHeat029Y00 = nativeHeat029Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat029Pass44]
  have h48 : nativeHeatPasses nativeGap030Old nativeHeat029Frames nativeHeat029Coef nativeHeat029Fixed nativeHeat029Base 48 nativeHeat029Y00 = nativeHeat029Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat029Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
