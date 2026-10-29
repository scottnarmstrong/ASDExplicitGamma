module
public import ASDExplicitGamma.Numerics.Native.Heat080Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat080Y00_formula : nativeHeat080Y00 = nativeHeat080Frames.y := by
  decide +kernel

theorem nativeHeat080All48 : nativeHeatPasses nativeGap081Old nativeHeat080Frames nativeHeat080Coef nativeHeat080Fixed nativeHeat080Base 48 nativeHeat080Frames.y = nativeHeat080Y48 := by
  rw [← nativeHeat080Y00_formula]
  have h4 : nativeHeatPasses nativeGap081Old nativeHeat080Frames nativeHeat080Coef nativeHeat080Fixed nativeHeat080Base 4 nativeHeat080Y00 = nativeHeat080Y04 := nativeHeat080Pass04
  have h8 : nativeHeatPasses nativeGap081Old nativeHeat080Frames nativeHeat080Coef nativeHeat080Fixed nativeHeat080Base 8 nativeHeat080Y00 = nativeHeat080Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat080Pass08]
  have h12 : nativeHeatPasses nativeGap081Old nativeHeat080Frames nativeHeat080Coef nativeHeat080Fixed nativeHeat080Base 12 nativeHeat080Y00 = nativeHeat080Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat080Pass12]
  have h16 : nativeHeatPasses nativeGap081Old nativeHeat080Frames nativeHeat080Coef nativeHeat080Fixed nativeHeat080Base 16 nativeHeat080Y00 = nativeHeat080Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat080Pass16]
  have h20 : nativeHeatPasses nativeGap081Old nativeHeat080Frames nativeHeat080Coef nativeHeat080Fixed nativeHeat080Base 20 nativeHeat080Y00 = nativeHeat080Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat080Pass20]
  have h24 : nativeHeatPasses nativeGap081Old nativeHeat080Frames nativeHeat080Coef nativeHeat080Fixed nativeHeat080Base 24 nativeHeat080Y00 = nativeHeat080Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat080Pass24]
  have h28 : nativeHeatPasses nativeGap081Old nativeHeat080Frames nativeHeat080Coef nativeHeat080Fixed nativeHeat080Base 28 nativeHeat080Y00 = nativeHeat080Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat080Pass28]
  have h32 : nativeHeatPasses nativeGap081Old nativeHeat080Frames nativeHeat080Coef nativeHeat080Fixed nativeHeat080Base 32 nativeHeat080Y00 = nativeHeat080Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat080Pass32]
  have h36 : nativeHeatPasses nativeGap081Old nativeHeat080Frames nativeHeat080Coef nativeHeat080Fixed nativeHeat080Base 36 nativeHeat080Y00 = nativeHeat080Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat080Pass36]
  have h40 : nativeHeatPasses nativeGap081Old nativeHeat080Frames nativeHeat080Coef nativeHeat080Fixed nativeHeat080Base 40 nativeHeat080Y00 = nativeHeat080Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat080Pass40]
  have h44 : nativeHeatPasses nativeGap081Old nativeHeat080Frames nativeHeat080Coef nativeHeat080Fixed nativeHeat080Base 44 nativeHeat080Y00 = nativeHeat080Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat080Pass44]
  have h48 : nativeHeatPasses nativeGap081Old nativeHeat080Frames nativeHeat080Coef nativeHeat080Fixed nativeHeat080Base 48 nativeHeat080Y00 = nativeHeat080Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat080Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
