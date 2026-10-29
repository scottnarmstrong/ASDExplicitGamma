module
public import ASDExplicitGamma.Numerics.Native.Heat056Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat056Y00_formula : nativeHeat056Y00 = nativeHeat056Frames.y := by
  decide +kernel

theorem nativeHeat056All48 : nativeHeatPasses nativeGap057Old nativeHeat056Frames nativeHeat056Coef nativeHeat056Fixed nativeHeat056Base 48 nativeHeat056Frames.y = nativeHeat056Y48 := by
  rw [← nativeHeat056Y00_formula]
  have h4 : nativeHeatPasses nativeGap057Old nativeHeat056Frames nativeHeat056Coef nativeHeat056Fixed nativeHeat056Base 4 nativeHeat056Y00 = nativeHeat056Y04 := nativeHeat056Pass04
  have h8 : nativeHeatPasses nativeGap057Old nativeHeat056Frames nativeHeat056Coef nativeHeat056Fixed nativeHeat056Base 8 nativeHeat056Y00 = nativeHeat056Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat056Pass08]
  have h12 : nativeHeatPasses nativeGap057Old nativeHeat056Frames nativeHeat056Coef nativeHeat056Fixed nativeHeat056Base 12 nativeHeat056Y00 = nativeHeat056Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat056Pass12]
  have h16 : nativeHeatPasses nativeGap057Old nativeHeat056Frames nativeHeat056Coef nativeHeat056Fixed nativeHeat056Base 16 nativeHeat056Y00 = nativeHeat056Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat056Pass16]
  have h20 : nativeHeatPasses nativeGap057Old nativeHeat056Frames nativeHeat056Coef nativeHeat056Fixed nativeHeat056Base 20 nativeHeat056Y00 = nativeHeat056Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat056Pass20]
  have h24 : nativeHeatPasses nativeGap057Old nativeHeat056Frames nativeHeat056Coef nativeHeat056Fixed nativeHeat056Base 24 nativeHeat056Y00 = nativeHeat056Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat056Pass24]
  have h28 : nativeHeatPasses nativeGap057Old nativeHeat056Frames nativeHeat056Coef nativeHeat056Fixed nativeHeat056Base 28 nativeHeat056Y00 = nativeHeat056Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat056Pass28]
  have h32 : nativeHeatPasses nativeGap057Old nativeHeat056Frames nativeHeat056Coef nativeHeat056Fixed nativeHeat056Base 32 nativeHeat056Y00 = nativeHeat056Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat056Pass32]
  have h36 : nativeHeatPasses nativeGap057Old nativeHeat056Frames nativeHeat056Coef nativeHeat056Fixed nativeHeat056Base 36 nativeHeat056Y00 = nativeHeat056Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat056Pass36]
  have h40 : nativeHeatPasses nativeGap057Old nativeHeat056Frames nativeHeat056Coef nativeHeat056Fixed nativeHeat056Base 40 nativeHeat056Y00 = nativeHeat056Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat056Pass40]
  have h44 : nativeHeatPasses nativeGap057Old nativeHeat056Frames nativeHeat056Coef nativeHeat056Fixed nativeHeat056Base 44 nativeHeat056Y00 = nativeHeat056Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat056Pass44]
  have h48 : nativeHeatPasses nativeGap057Old nativeHeat056Frames nativeHeat056Coef nativeHeat056Fixed nativeHeat056Base 48 nativeHeat056Y00 = nativeHeat056Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat056Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
