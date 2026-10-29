module
public import ASDExplicitGamma.Numerics.Native.Heat152Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat152Y00_formula : nativeHeat152Y00 = nativeHeat152Frames.y := by
  decide +kernel

theorem nativeHeat152All48 : nativeHeatPasses nativeGap153Old nativeHeat152Frames nativeHeat152Coef nativeHeat152Fixed nativeHeat152Base 48 nativeHeat152Frames.y = nativeHeat152Y48 := by
  rw [← nativeHeat152Y00_formula]
  have h4 : nativeHeatPasses nativeGap153Old nativeHeat152Frames nativeHeat152Coef nativeHeat152Fixed nativeHeat152Base 4 nativeHeat152Y00 = nativeHeat152Y04 := nativeHeat152Pass04
  have h8 : nativeHeatPasses nativeGap153Old nativeHeat152Frames nativeHeat152Coef nativeHeat152Fixed nativeHeat152Base 8 nativeHeat152Y00 = nativeHeat152Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat152Pass08]
  have h12 : nativeHeatPasses nativeGap153Old nativeHeat152Frames nativeHeat152Coef nativeHeat152Fixed nativeHeat152Base 12 nativeHeat152Y00 = nativeHeat152Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat152Pass12]
  have h16 : nativeHeatPasses nativeGap153Old nativeHeat152Frames nativeHeat152Coef nativeHeat152Fixed nativeHeat152Base 16 nativeHeat152Y00 = nativeHeat152Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat152Pass16]
  have h20 : nativeHeatPasses nativeGap153Old nativeHeat152Frames nativeHeat152Coef nativeHeat152Fixed nativeHeat152Base 20 nativeHeat152Y00 = nativeHeat152Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat152Pass20]
  have h24 : nativeHeatPasses nativeGap153Old nativeHeat152Frames nativeHeat152Coef nativeHeat152Fixed nativeHeat152Base 24 nativeHeat152Y00 = nativeHeat152Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat152Pass24]
  have h28 : nativeHeatPasses nativeGap153Old nativeHeat152Frames nativeHeat152Coef nativeHeat152Fixed nativeHeat152Base 28 nativeHeat152Y00 = nativeHeat152Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat152Pass28]
  have h32 : nativeHeatPasses nativeGap153Old nativeHeat152Frames nativeHeat152Coef nativeHeat152Fixed nativeHeat152Base 32 nativeHeat152Y00 = nativeHeat152Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat152Pass32]
  have h36 : nativeHeatPasses nativeGap153Old nativeHeat152Frames nativeHeat152Coef nativeHeat152Fixed nativeHeat152Base 36 nativeHeat152Y00 = nativeHeat152Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat152Pass36]
  have h40 : nativeHeatPasses nativeGap153Old nativeHeat152Frames nativeHeat152Coef nativeHeat152Fixed nativeHeat152Base 40 nativeHeat152Y00 = nativeHeat152Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat152Pass40]
  have h44 : nativeHeatPasses nativeGap153Old nativeHeat152Frames nativeHeat152Coef nativeHeat152Fixed nativeHeat152Base 44 nativeHeat152Y00 = nativeHeat152Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat152Pass44]
  have h48 : nativeHeatPasses nativeGap153Old nativeHeat152Frames nativeHeat152Coef nativeHeat152Fixed nativeHeat152Base 48 nativeHeat152Y00 = nativeHeat152Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat152Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
