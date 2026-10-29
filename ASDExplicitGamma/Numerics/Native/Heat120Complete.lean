module
public import ASDExplicitGamma.Numerics.Native.Heat120Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat120Y00_formula : nativeHeat120Y00 = nativeHeat120Frames.y := by
  decide +kernel

theorem nativeHeat120All48 : nativeHeatPasses nativeGap121Old nativeHeat120Frames nativeHeat120Coef nativeHeat120Fixed nativeHeat120Base 48 nativeHeat120Frames.y = nativeHeat120Y48 := by
  rw [← nativeHeat120Y00_formula]
  have h4 : nativeHeatPasses nativeGap121Old nativeHeat120Frames nativeHeat120Coef nativeHeat120Fixed nativeHeat120Base 4 nativeHeat120Y00 = nativeHeat120Y04 := nativeHeat120Pass04
  have h8 : nativeHeatPasses nativeGap121Old nativeHeat120Frames nativeHeat120Coef nativeHeat120Fixed nativeHeat120Base 8 nativeHeat120Y00 = nativeHeat120Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat120Pass08]
  have h12 : nativeHeatPasses nativeGap121Old nativeHeat120Frames nativeHeat120Coef nativeHeat120Fixed nativeHeat120Base 12 nativeHeat120Y00 = nativeHeat120Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat120Pass12]
  have h16 : nativeHeatPasses nativeGap121Old nativeHeat120Frames nativeHeat120Coef nativeHeat120Fixed nativeHeat120Base 16 nativeHeat120Y00 = nativeHeat120Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat120Pass16]
  have h20 : nativeHeatPasses nativeGap121Old nativeHeat120Frames nativeHeat120Coef nativeHeat120Fixed nativeHeat120Base 20 nativeHeat120Y00 = nativeHeat120Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat120Pass20]
  have h24 : nativeHeatPasses nativeGap121Old nativeHeat120Frames nativeHeat120Coef nativeHeat120Fixed nativeHeat120Base 24 nativeHeat120Y00 = nativeHeat120Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat120Pass24]
  have h28 : nativeHeatPasses nativeGap121Old nativeHeat120Frames nativeHeat120Coef nativeHeat120Fixed nativeHeat120Base 28 nativeHeat120Y00 = nativeHeat120Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat120Pass28]
  have h32 : nativeHeatPasses nativeGap121Old nativeHeat120Frames nativeHeat120Coef nativeHeat120Fixed nativeHeat120Base 32 nativeHeat120Y00 = nativeHeat120Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat120Pass32]
  have h36 : nativeHeatPasses nativeGap121Old nativeHeat120Frames nativeHeat120Coef nativeHeat120Fixed nativeHeat120Base 36 nativeHeat120Y00 = nativeHeat120Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat120Pass36]
  have h40 : nativeHeatPasses nativeGap121Old nativeHeat120Frames nativeHeat120Coef nativeHeat120Fixed nativeHeat120Base 40 nativeHeat120Y00 = nativeHeat120Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat120Pass40]
  have h44 : nativeHeatPasses nativeGap121Old nativeHeat120Frames nativeHeat120Coef nativeHeat120Fixed nativeHeat120Base 44 nativeHeat120Y00 = nativeHeat120Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat120Pass44]
  have h48 : nativeHeatPasses nativeGap121Old nativeHeat120Frames nativeHeat120Coef nativeHeat120Fixed nativeHeat120Base 48 nativeHeat120Y00 = nativeHeat120Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat120Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
