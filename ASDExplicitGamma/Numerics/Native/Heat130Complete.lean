module
public import ASDExplicitGamma.Numerics.Native.Heat130Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat130Y00_formula : nativeHeat130Y00 = nativeHeat130Frames.y := by
  decide +kernel

theorem nativeHeat130All48 : nativeHeatPasses nativeGap131Old nativeHeat130Frames nativeHeat130Coef nativeHeat130Fixed nativeHeat130Base 48 nativeHeat130Frames.y = nativeHeat130Y48 := by
  rw [← nativeHeat130Y00_formula]
  have h4 : nativeHeatPasses nativeGap131Old nativeHeat130Frames nativeHeat130Coef nativeHeat130Fixed nativeHeat130Base 4 nativeHeat130Y00 = nativeHeat130Y04 := nativeHeat130Pass04
  have h8 : nativeHeatPasses nativeGap131Old nativeHeat130Frames nativeHeat130Coef nativeHeat130Fixed nativeHeat130Base 8 nativeHeat130Y00 = nativeHeat130Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat130Pass08]
  have h12 : nativeHeatPasses nativeGap131Old nativeHeat130Frames nativeHeat130Coef nativeHeat130Fixed nativeHeat130Base 12 nativeHeat130Y00 = nativeHeat130Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat130Pass12]
  have h16 : nativeHeatPasses nativeGap131Old nativeHeat130Frames nativeHeat130Coef nativeHeat130Fixed nativeHeat130Base 16 nativeHeat130Y00 = nativeHeat130Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat130Pass16]
  have h20 : nativeHeatPasses nativeGap131Old nativeHeat130Frames nativeHeat130Coef nativeHeat130Fixed nativeHeat130Base 20 nativeHeat130Y00 = nativeHeat130Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat130Pass20]
  have h24 : nativeHeatPasses nativeGap131Old nativeHeat130Frames nativeHeat130Coef nativeHeat130Fixed nativeHeat130Base 24 nativeHeat130Y00 = nativeHeat130Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat130Pass24]
  have h28 : nativeHeatPasses nativeGap131Old nativeHeat130Frames nativeHeat130Coef nativeHeat130Fixed nativeHeat130Base 28 nativeHeat130Y00 = nativeHeat130Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat130Pass28]
  have h32 : nativeHeatPasses nativeGap131Old nativeHeat130Frames nativeHeat130Coef nativeHeat130Fixed nativeHeat130Base 32 nativeHeat130Y00 = nativeHeat130Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat130Pass32]
  have h36 : nativeHeatPasses nativeGap131Old nativeHeat130Frames nativeHeat130Coef nativeHeat130Fixed nativeHeat130Base 36 nativeHeat130Y00 = nativeHeat130Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat130Pass36]
  have h40 : nativeHeatPasses nativeGap131Old nativeHeat130Frames nativeHeat130Coef nativeHeat130Fixed nativeHeat130Base 40 nativeHeat130Y00 = nativeHeat130Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat130Pass40]
  have h44 : nativeHeatPasses nativeGap131Old nativeHeat130Frames nativeHeat130Coef nativeHeat130Fixed nativeHeat130Base 44 nativeHeat130Y00 = nativeHeat130Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat130Pass44]
  have h48 : nativeHeatPasses nativeGap131Old nativeHeat130Frames nativeHeat130Coef nativeHeat130Fixed nativeHeat130Base 48 nativeHeat130Y00 = nativeHeat130Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat130Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
