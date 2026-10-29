module
public import ASDExplicitGamma.Numerics.Native.Heat156Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat156Y00_formula : nativeHeat156Y00 = nativeHeat156Frames.y := by
  decide +kernel

theorem nativeHeat156All48 : nativeHeatPasses nativeGap157Old nativeHeat156Frames nativeHeat156Coef nativeHeat156Fixed nativeHeat156Base 48 nativeHeat156Frames.y = nativeHeat156Y48 := by
  rw [← nativeHeat156Y00_formula]
  have h4 : nativeHeatPasses nativeGap157Old nativeHeat156Frames nativeHeat156Coef nativeHeat156Fixed nativeHeat156Base 4 nativeHeat156Y00 = nativeHeat156Y04 := nativeHeat156Pass04
  have h8 : nativeHeatPasses nativeGap157Old nativeHeat156Frames nativeHeat156Coef nativeHeat156Fixed nativeHeat156Base 8 nativeHeat156Y00 = nativeHeat156Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat156Pass08]
  have h12 : nativeHeatPasses nativeGap157Old nativeHeat156Frames nativeHeat156Coef nativeHeat156Fixed nativeHeat156Base 12 nativeHeat156Y00 = nativeHeat156Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat156Pass12]
  have h16 : nativeHeatPasses nativeGap157Old nativeHeat156Frames nativeHeat156Coef nativeHeat156Fixed nativeHeat156Base 16 nativeHeat156Y00 = nativeHeat156Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat156Pass16]
  have h20 : nativeHeatPasses nativeGap157Old nativeHeat156Frames nativeHeat156Coef nativeHeat156Fixed nativeHeat156Base 20 nativeHeat156Y00 = nativeHeat156Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat156Pass20]
  have h24 : nativeHeatPasses nativeGap157Old nativeHeat156Frames nativeHeat156Coef nativeHeat156Fixed nativeHeat156Base 24 nativeHeat156Y00 = nativeHeat156Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat156Pass24]
  have h28 : nativeHeatPasses nativeGap157Old nativeHeat156Frames nativeHeat156Coef nativeHeat156Fixed nativeHeat156Base 28 nativeHeat156Y00 = nativeHeat156Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat156Pass28]
  have h32 : nativeHeatPasses nativeGap157Old nativeHeat156Frames nativeHeat156Coef nativeHeat156Fixed nativeHeat156Base 32 nativeHeat156Y00 = nativeHeat156Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat156Pass32]
  have h36 : nativeHeatPasses nativeGap157Old nativeHeat156Frames nativeHeat156Coef nativeHeat156Fixed nativeHeat156Base 36 nativeHeat156Y00 = nativeHeat156Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat156Pass36]
  have h40 : nativeHeatPasses nativeGap157Old nativeHeat156Frames nativeHeat156Coef nativeHeat156Fixed nativeHeat156Base 40 nativeHeat156Y00 = nativeHeat156Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat156Pass40]
  have h44 : nativeHeatPasses nativeGap157Old nativeHeat156Frames nativeHeat156Coef nativeHeat156Fixed nativeHeat156Base 44 nativeHeat156Y00 = nativeHeat156Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat156Pass44]
  have h48 : nativeHeatPasses nativeGap157Old nativeHeat156Frames nativeHeat156Coef nativeHeat156Fixed nativeHeat156Base 48 nativeHeat156Y00 = nativeHeat156Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat156Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
