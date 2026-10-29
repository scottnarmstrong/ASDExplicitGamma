module
public import ASDExplicitGamma.Numerics.Native.Heat093Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat093Y00_formula : nativeHeat093Y00 = nativeHeat093Frames.y := by
  decide +kernel

theorem nativeHeat093All48 : nativeHeatPasses nativeGap094Old nativeHeat093Frames nativeHeat093Coef nativeHeat093Fixed nativeHeat093Base 48 nativeHeat093Frames.y = nativeHeat093Y48 := by
  rw [← nativeHeat093Y00_formula]
  have h4 : nativeHeatPasses nativeGap094Old nativeHeat093Frames nativeHeat093Coef nativeHeat093Fixed nativeHeat093Base 4 nativeHeat093Y00 = nativeHeat093Y04 := nativeHeat093Pass04
  have h8 : nativeHeatPasses nativeGap094Old nativeHeat093Frames nativeHeat093Coef nativeHeat093Fixed nativeHeat093Base 8 nativeHeat093Y00 = nativeHeat093Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat093Pass08]
  have h12 : nativeHeatPasses nativeGap094Old nativeHeat093Frames nativeHeat093Coef nativeHeat093Fixed nativeHeat093Base 12 nativeHeat093Y00 = nativeHeat093Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat093Pass12]
  have h16 : nativeHeatPasses nativeGap094Old nativeHeat093Frames nativeHeat093Coef nativeHeat093Fixed nativeHeat093Base 16 nativeHeat093Y00 = nativeHeat093Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat093Pass16]
  have h20 : nativeHeatPasses nativeGap094Old nativeHeat093Frames nativeHeat093Coef nativeHeat093Fixed nativeHeat093Base 20 nativeHeat093Y00 = nativeHeat093Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat093Pass20]
  have h24 : nativeHeatPasses nativeGap094Old nativeHeat093Frames nativeHeat093Coef nativeHeat093Fixed nativeHeat093Base 24 nativeHeat093Y00 = nativeHeat093Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat093Pass24]
  have h28 : nativeHeatPasses nativeGap094Old nativeHeat093Frames nativeHeat093Coef nativeHeat093Fixed nativeHeat093Base 28 nativeHeat093Y00 = nativeHeat093Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat093Pass28]
  have h32 : nativeHeatPasses nativeGap094Old nativeHeat093Frames nativeHeat093Coef nativeHeat093Fixed nativeHeat093Base 32 nativeHeat093Y00 = nativeHeat093Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat093Pass32]
  have h36 : nativeHeatPasses nativeGap094Old nativeHeat093Frames nativeHeat093Coef nativeHeat093Fixed nativeHeat093Base 36 nativeHeat093Y00 = nativeHeat093Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat093Pass36]
  have h40 : nativeHeatPasses nativeGap094Old nativeHeat093Frames nativeHeat093Coef nativeHeat093Fixed nativeHeat093Base 40 nativeHeat093Y00 = nativeHeat093Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat093Pass40]
  have h44 : nativeHeatPasses nativeGap094Old nativeHeat093Frames nativeHeat093Coef nativeHeat093Fixed nativeHeat093Base 44 nativeHeat093Y00 = nativeHeat093Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat093Pass44]
  have h48 : nativeHeatPasses nativeGap094Old nativeHeat093Frames nativeHeat093Coef nativeHeat093Fixed nativeHeat093Base 48 nativeHeat093Y00 = nativeHeat093Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat093Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
