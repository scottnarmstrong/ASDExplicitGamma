module
public import ASDExplicitGamma.Numerics.Native.Heat018Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat018Y00_formula : nativeHeat018Y00 = nativeHeat018Frames.y := by
  decide +kernel

theorem nativeHeat018All48 : nativeHeatPasses nativeGap019Old nativeHeat018Frames nativeHeat018Coef nativeHeat018Fixed nativeHeat018Base 48 nativeHeat018Frames.y = nativeHeat018Y48 := by
  rw [← nativeHeat018Y00_formula]
  have h4 : nativeHeatPasses nativeGap019Old nativeHeat018Frames nativeHeat018Coef nativeHeat018Fixed nativeHeat018Base 4 nativeHeat018Y00 = nativeHeat018Y04 := nativeHeat018Pass04
  have h8 : nativeHeatPasses nativeGap019Old nativeHeat018Frames nativeHeat018Coef nativeHeat018Fixed nativeHeat018Base 8 nativeHeat018Y00 = nativeHeat018Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat018Pass08]
  have h12 : nativeHeatPasses nativeGap019Old nativeHeat018Frames nativeHeat018Coef nativeHeat018Fixed nativeHeat018Base 12 nativeHeat018Y00 = nativeHeat018Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat018Pass12]
  have h16 : nativeHeatPasses nativeGap019Old nativeHeat018Frames nativeHeat018Coef nativeHeat018Fixed nativeHeat018Base 16 nativeHeat018Y00 = nativeHeat018Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat018Pass16]
  have h20 : nativeHeatPasses nativeGap019Old nativeHeat018Frames nativeHeat018Coef nativeHeat018Fixed nativeHeat018Base 20 nativeHeat018Y00 = nativeHeat018Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat018Pass20]
  have h24 : nativeHeatPasses nativeGap019Old nativeHeat018Frames nativeHeat018Coef nativeHeat018Fixed nativeHeat018Base 24 nativeHeat018Y00 = nativeHeat018Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat018Pass24]
  have h28 : nativeHeatPasses nativeGap019Old nativeHeat018Frames nativeHeat018Coef nativeHeat018Fixed nativeHeat018Base 28 nativeHeat018Y00 = nativeHeat018Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat018Pass28]
  have h32 : nativeHeatPasses nativeGap019Old nativeHeat018Frames nativeHeat018Coef nativeHeat018Fixed nativeHeat018Base 32 nativeHeat018Y00 = nativeHeat018Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat018Pass32]
  have h36 : nativeHeatPasses nativeGap019Old nativeHeat018Frames nativeHeat018Coef nativeHeat018Fixed nativeHeat018Base 36 nativeHeat018Y00 = nativeHeat018Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat018Pass36]
  have h40 : nativeHeatPasses nativeGap019Old nativeHeat018Frames nativeHeat018Coef nativeHeat018Fixed nativeHeat018Base 40 nativeHeat018Y00 = nativeHeat018Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat018Pass40]
  have h44 : nativeHeatPasses nativeGap019Old nativeHeat018Frames nativeHeat018Coef nativeHeat018Fixed nativeHeat018Base 44 nativeHeat018Y00 = nativeHeat018Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat018Pass44]
  have h48 : nativeHeatPasses nativeGap019Old nativeHeat018Frames nativeHeat018Coef nativeHeat018Fixed nativeHeat018Base 48 nativeHeat018Y00 = nativeHeat018Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat018Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
