module
public import ASDExplicitGamma.Numerics.Native.Heat153Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat153Y00_formula : nativeHeat153Y00 = nativeHeat153Frames.y := by
  decide +kernel

theorem nativeHeat153All48 : nativeHeatPasses nativeGap154Old nativeHeat153Frames nativeHeat153Coef nativeHeat153Fixed nativeHeat153Base 48 nativeHeat153Frames.y = nativeHeat153Y48 := by
  rw [← nativeHeat153Y00_formula]
  have h4 : nativeHeatPasses nativeGap154Old nativeHeat153Frames nativeHeat153Coef nativeHeat153Fixed nativeHeat153Base 4 nativeHeat153Y00 = nativeHeat153Y04 := nativeHeat153Pass04
  have h8 : nativeHeatPasses nativeGap154Old nativeHeat153Frames nativeHeat153Coef nativeHeat153Fixed nativeHeat153Base 8 nativeHeat153Y00 = nativeHeat153Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat153Pass08]
  have h12 : nativeHeatPasses nativeGap154Old nativeHeat153Frames nativeHeat153Coef nativeHeat153Fixed nativeHeat153Base 12 nativeHeat153Y00 = nativeHeat153Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat153Pass12]
  have h16 : nativeHeatPasses nativeGap154Old nativeHeat153Frames nativeHeat153Coef nativeHeat153Fixed nativeHeat153Base 16 nativeHeat153Y00 = nativeHeat153Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat153Pass16]
  have h20 : nativeHeatPasses nativeGap154Old nativeHeat153Frames nativeHeat153Coef nativeHeat153Fixed nativeHeat153Base 20 nativeHeat153Y00 = nativeHeat153Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat153Pass20]
  have h24 : nativeHeatPasses nativeGap154Old nativeHeat153Frames nativeHeat153Coef nativeHeat153Fixed nativeHeat153Base 24 nativeHeat153Y00 = nativeHeat153Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat153Pass24]
  have h28 : nativeHeatPasses nativeGap154Old nativeHeat153Frames nativeHeat153Coef nativeHeat153Fixed nativeHeat153Base 28 nativeHeat153Y00 = nativeHeat153Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat153Pass28]
  have h32 : nativeHeatPasses nativeGap154Old nativeHeat153Frames nativeHeat153Coef nativeHeat153Fixed nativeHeat153Base 32 nativeHeat153Y00 = nativeHeat153Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat153Pass32]
  have h36 : nativeHeatPasses nativeGap154Old nativeHeat153Frames nativeHeat153Coef nativeHeat153Fixed nativeHeat153Base 36 nativeHeat153Y00 = nativeHeat153Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat153Pass36]
  have h40 : nativeHeatPasses nativeGap154Old nativeHeat153Frames nativeHeat153Coef nativeHeat153Fixed nativeHeat153Base 40 nativeHeat153Y00 = nativeHeat153Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat153Pass40]
  have h44 : nativeHeatPasses nativeGap154Old nativeHeat153Frames nativeHeat153Coef nativeHeat153Fixed nativeHeat153Base 44 nativeHeat153Y00 = nativeHeat153Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat153Pass44]
  have h48 : nativeHeatPasses nativeGap154Old nativeHeat153Frames nativeHeat153Coef nativeHeat153Fixed nativeHeat153Base 48 nativeHeat153Y00 = nativeHeat153Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat153Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
