module
public import ASDExplicitGamma.Numerics.Native.Heat055Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat055Y00_formula : nativeHeat055Y00 = nativeHeat055Frames.y := by
  decide +kernel

theorem nativeHeat055All48 : nativeHeatPasses nativeGap056Old nativeHeat055Frames nativeHeat055Coef nativeHeat055Fixed nativeHeat055Base 48 nativeHeat055Frames.y = nativeHeat055Y48 := by
  rw [← nativeHeat055Y00_formula]
  have h4 : nativeHeatPasses nativeGap056Old nativeHeat055Frames nativeHeat055Coef nativeHeat055Fixed nativeHeat055Base 4 nativeHeat055Y00 = nativeHeat055Y04 := nativeHeat055Pass04
  have h8 : nativeHeatPasses nativeGap056Old nativeHeat055Frames nativeHeat055Coef nativeHeat055Fixed nativeHeat055Base 8 nativeHeat055Y00 = nativeHeat055Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat055Pass08]
  have h12 : nativeHeatPasses nativeGap056Old nativeHeat055Frames nativeHeat055Coef nativeHeat055Fixed nativeHeat055Base 12 nativeHeat055Y00 = nativeHeat055Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat055Pass12]
  have h16 : nativeHeatPasses nativeGap056Old nativeHeat055Frames nativeHeat055Coef nativeHeat055Fixed nativeHeat055Base 16 nativeHeat055Y00 = nativeHeat055Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat055Pass16]
  have h20 : nativeHeatPasses nativeGap056Old nativeHeat055Frames nativeHeat055Coef nativeHeat055Fixed nativeHeat055Base 20 nativeHeat055Y00 = nativeHeat055Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat055Pass20]
  have h24 : nativeHeatPasses nativeGap056Old nativeHeat055Frames nativeHeat055Coef nativeHeat055Fixed nativeHeat055Base 24 nativeHeat055Y00 = nativeHeat055Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat055Pass24]
  have h28 : nativeHeatPasses nativeGap056Old nativeHeat055Frames nativeHeat055Coef nativeHeat055Fixed nativeHeat055Base 28 nativeHeat055Y00 = nativeHeat055Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat055Pass28]
  have h32 : nativeHeatPasses nativeGap056Old nativeHeat055Frames nativeHeat055Coef nativeHeat055Fixed nativeHeat055Base 32 nativeHeat055Y00 = nativeHeat055Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat055Pass32]
  have h36 : nativeHeatPasses nativeGap056Old nativeHeat055Frames nativeHeat055Coef nativeHeat055Fixed nativeHeat055Base 36 nativeHeat055Y00 = nativeHeat055Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat055Pass36]
  have h40 : nativeHeatPasses nativeGap056Old nativeHeat055Frames nativeHeat055Coef nativeHeat055Fixed nativeHeat055Base 40 nativeHeat055Y00 = nativeHeat055Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat055Pass40]
  have h44 : nativeHeatPasses nativeGap056Old nativeHeat055Frames nativeHeat055Coef nativeHeat055Fixed nativeHeat055Base 44 nativeHeat055Y00 = nativeHeat055Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat055Pass44]
  have h48 : nativeHeatPasses nativeGap056Old nativeHeat055Frames nativeHeat055Coef nativeHeat055Fixed nativeHeat055Base 48 nativeHeat055Y00 = nativeHeat055Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat055Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
