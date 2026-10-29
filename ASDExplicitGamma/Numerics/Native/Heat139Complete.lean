module
public import ASDExplicitGamma.Numerics.Native.Heat139Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat139Y00_formula : nativeHeat139Y00 = nativeHeat139Frames.y := by
  decide +kernel

theorem nativeHeat139All48 : nativeHeatPasses nativeGap140Old nativeHeat139Frames nativeHeat139Coef nativeHeat139Fixed nativeHeat139Base 48 nativeHeat139Frames.y = nativeHeat139Y48 := by
  rw [← nativeHeat139Y00_formula]
  have h4 : nativeHeatPasses nativeGap140Old nativeHeat139Frames nativeHeat139Coef nativeHeat139Fixed nativeHeat139Base 4 nativeHeat139Y00 = nativeHeat139Y04 := nativeHeat139Pass04
  have h8 : nativeHeatPasses nativeGap140Old nativeHeat139Frames nativeHeat139Coef nativeHeat139Fixed nativeHeat139Base 8 nativeHeat139Y00 = nativeHeat139Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat139Pass08]
  have h12 : nativeHeatPasses nativeGap140Old nativeHeat139Frames nativeHeat139Coef nativeHeat139Fixed nativeHeat139Base 12 nativeHeat139Y00 = nativeHeat139Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat139Pass12]
  have h16 : nativeHeatPasses nativeGap140Old nativeHeat139Frames nativeHeat139Coef nativeHeat139Fixed nativeHeat139Base 16 nativeHeat139Y00 = nativeHeat139Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat139Pass16]
  have h20 : nativeHeatPasses nativeGap140Old nativeHeat139Frames nativeHeat139Coef nativeHeat139Fixed nativeHeat139Base 20 nativeHeat139Y00 = nativeHeat139Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat139Pass20]
  have h24 : nativeHeatPasses nativeGap140Old nativeHeat139Frames nativeHeat139Coef nativeHeat139Fixed nativeHeat139Base 24 nativeHeat139Y00 = nativeHeat139Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat139Pass24]
  have h28 : nativeHeatPasses nativeGap140Old nativeHeat139Frames nativeHeat139Coef nativeHeat139Fixed nativeHeat139Base 28 nativeHeat139Y00 = nativeHeat139Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat139Pass28]
  have h32 : nativeHeatPasses nativeGap140Old nativeHeat139Frames nativeHeat139Coef nativeHeat139Fixed nativeHeat139Base 32 nativeHeat139Y00 = nativeHeat139Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat139Pass32]
  have h36 : nativeHeatPasses nativeGap140Old nativeHeat139Frames nativeHeat139Coef nativeHeat139Fixed nativeHeat139Base 36 nativeHeat139Y00 = nativeHeat139Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat139Pass36]
  have h40 : nativeHeatPasses nativeGap140Old nativeHeat139Frames nativeHeat139Coef nativeHeat139Fixed nativeHeat139Base 40 nativeHeat139Y00 = nativeHeat139Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat139Pass40]
  have h44 : nativeHeatPasses nativeGap140Old nativeHeat139Frames nativeHeat139Coef nativeHeat139Fixed nativeHeat139Base 44 nativeHeat139Y00 = nativeHeat139Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat139Pass44]
  have h48 : nativeHeatPasses nativeGap140Old nativeHeat139Frames nativeHeat139Coef nativeHeat139Fixed nativeHeat139Base 48 nativeHeat139Y00 = nativeHeat139Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat139Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
