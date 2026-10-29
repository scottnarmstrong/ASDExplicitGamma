module
public import ASDExplicitGamma.Numerics.Native.Heat022Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat022Y00_formula : nativeHeat022Y00 = nativeHeat022Frames.y := by
  decide +kernel

theorem nativeHeat022All48 : nativeHeatPasses nativeGap023Old nativeHeat022Frames nativeHeat022Coef nativeHeat022Fixed nativeHeat022Base 48 nativeHeat022Frames.y = nativeHeat022Y48 := by
  rw [← nativeHeat022Y00_formula]
  have h4 : nativeHeatPasses nativeGap023Old nativeHeat022Frames nativeHeat022Coef nativeHeat022Fixed nativeHeat022Base 4 nativeHeat022Y00 = nativeHeat022Y04 := nativeHeat022Pass04
  have h8 : nativeHeatPasses nativeGap023Old nativeHeat022Frames nativeHeat022Coef nativeHeat022Fixed nativeHeat022Base 8 nativeHeat022Y00 = nativeHeat022Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat022Pass08]
  have h12 : nativeHeatPasses nativeGap023Old nativeHeat022Frames nativeHeat022Coef nativeHeat022Fixed nativeHeat022Base 12 nativeHeat022Y00 = nativeHeat022Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat022Pass12]
  have h16 : nativeHeatPasses nativeGap023Old nativeHeat022Frames nativeHeat022Coef nativeHeat022Fixed nativeHeat022Base 16 nativeHeat022Y00 = nativeHeat022Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat022Pass16]
  have h20 : nativeHeatPasses nativeGap023Old nativeHeat022Frames nativeHeat022Coef nativeHeat022Fixed nativeHeat022Base 20 nativeHeat022Y00 = nativeHeat022Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat022Pass20]
  have h24 : nativeHeatPasses nativeGap023Old nativeHeat022Frames nativeHeat022Coef nativeHeat022Fixed nativeHeat022Base 24 nativeHeat022Y00 = nativeHeat022Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat022Pass24]
  have h28 : nativeHeatPasses nativeGap023Old nativeHeat022Frames nativeHeat022Coef nativeHeat022Fixed nativeHeat022Base 28 nativeHeat022Y00 = nativeHeat022Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat022Pass28]
  have h32 : nativeHeatPasses nativeGap023Old nativeHeat022Frames nativeHeat022Coef nativeHeat022Fixed nativeHeat022Base 32 nativeHeat022Y00 = nativeHeat022Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat022Pass32]
  have h36 : nativeHeatPasses nativeGap023Old nativeHeat022Frames nativeHeat022Coef nativeHeat022Fixed nativeHeat022Base 36 nativeHeat022Y00 = nativeHeat022Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat022Pass36]
  have h40 : nativeHeatPasses nativeGap023Old nativeHeat022Frames nativeHeat022Coef nativeHeat022Fixed nativeHeat022Base 40 nativeHeat022Y00 = nativeHeat022Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat022Pass40]
  have h44 : nativeHeatPasses nativeGap023Old nativeHeat022Frames nativeHeat022Coef nativeHeat022Fixed nativeHeat022Base 44 nativeHeat022Y00 = nativeHeat022Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat022Pass44]
  have h48 : nativeHeatPasses nativeGap023Old nativeHeat022Frames nativeHeat022Coef nativeHeat022Fixed nativeHeat022Base 48 nativeHeat022Y00 = nativeHeat022Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat022Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
