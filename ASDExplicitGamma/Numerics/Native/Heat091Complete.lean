module
public import ASDExplicitGamma.Numerics.Native.Heat091Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat091Y00_formula : nativeHeat091Y00 = nativeHeat091Frames.y := by
  decide +kernel

theorem nativeHeat091All48 : nativeHeatPasses nativeGap092Old nativeHeat091Frames nativeHeat091Coef nativeHeat091Fixed nativeHeat091Base 48 nativeHeat091Frames.y = nativeHeat091Y48 := by
  rw [← nativeHeat091Y00_formula]
  have h4 : nativeHeatPasses nativeGap092Old nativeHeat091Frames nativeHeat091Coef nativeHeat091Fixed nativeHeat091Base 4 nativeHeat091Y00 = nativeHeat091Y04 := nativeHeat091Pass04
  have h8 : nativeHeatPasses nativeGap092Old nativeHeat091Frames nativeHeat091Coef nativeHeat091Fixed nativeHeat091Base 8 nativeHeat091Y00 = nativeHeat091Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat091Pass08]
  have h12 : nativeHeatPasses nativeGap092Old nativeHeat091Frames nativeHeat091Coef nativeHeat091Fixed nativeHeat091Base 12 nativeHeat091Y00 = nativeHeat091Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat091Pass12]
  have h16 : nativeHeatPasses nativeGap092Old nativeHeat091Frames nativeHeat091Coef nativeHeat091Fixed nativeHeat091Base 16 nativeHeat091Y00 = nativeHeat091Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat091Pass16]
  have h20 : nativeHeatPasses nativeGap092Old nativeHeat091Frames nativeHeat091Coef nativeHeat091Fixed nativeHeat091Base 20 nativeHeat091Y00 = nativeHeat091Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat091Pass20]
  have h24 : nativeHeatPasses nativeGap092Old nativeHeat091Frames nativeHeat091Coef nativeHeat091Fixed nativeHeat091Base 24 nativeHeat091Y00 = nativeHeat091Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat091Pass24]
  have h28 : nativeHeatPasses nativeGap092Old nativeHeat091Frames nativeHeat091Coef nativeHeat091Fixed nativeHeat091Base 28 nativeHeat091Y00 = nativeHeat091Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat091Pass28]
  have h32 : nativeHeatPasses nativeGap092Old nativeHeat091Frames nativeHeat091Coef nativeHeat091Fixed nativeHeat091Base 32 nativeHeat091Y00 = nativeHeat091Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat091Pass32]
  have h36 : nativeHeatPasses nativeGap092Old nativeHeat091Frames nativeHeat091Coef nativeHeat091Fixed nativeHeat091Base 36 nativeHeat091Y00 = nativeHeat091Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat091Pass36]
  have h40 : nativeHeatPasses nativeGap092Old nativeHeat091Frames nativeHeat091Coef nativeHeat091Fixed nativeHeat091Base 40 nativeHeat091Y00 = nativeHeat091Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat091Pass40]
  have h44 : nativeHeatPasses nativeGap092Old nativeHeat091Frames nativeHeat091Coef nativeHeat091Fixed nativeHeat091Base 44 nativeHeat091Y00 = nativeHeat091Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat091Pass44]
  have h48 : nativeHeatPasses nativeGap092Old nativeHeat091Frames nativeHeat091Coef nativeHeat091Fixed nativeHeat091Base 48 nativeHeat091Y00 = nativeHeat091Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat091Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
