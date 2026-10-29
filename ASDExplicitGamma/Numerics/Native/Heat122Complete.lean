module
public import ASDExplicitGamma.Numerics.Native.Heat122Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat122Y00_formula : nativeHeat122Y00 = nativeHeat122Frames.y := by
  decide +kernel

theorem nativeHeat122All48 : nativeHeatPasses nativeGap123Old nativeHeat122Frames nativeHeat122Coef nativeHeat122Fixed nativeHeat122Base 48 nativeHeat122Frames.y = nativeHeat122Y48 := by
  rw [← nativeHeat122Y00_formula]
  have h4 : nativeHeatPasses nativeGap123Old nativeHeat122Frames nativeHeat122Coef nativeHeat122Fixed nativeHeat122Base 4 nativeHeat122Y00 = nativeHeat122Y04 := nativeHeat122Pass04
  have h8 : nativeHeatPasses nativeGap123Old nativeHeat122Frames nativeHeat122Coef nativeHeat122Fixed nativeHeat122Base 8 nativeHeat122Y00 = nativeHeat122Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat122Pass08]
  have h12 : nativeHeatPasses nativeGap123Old nativeHeat122Frames nativeHeat122Coef nativeHeat122Fixed nativeHeat122Base 12 nativeHeat122Y00 = nativeHeat122Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat122Pass12]
  have h16 : nativeHeatPasses nativeGap123Old nativeHeat122Frames nativeHeat122Coef nativeHeat122Fixed nativeHeat122Base 16 nativeHeat122Y00 = nativeHeat122Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat122Pass16]
  have h20 : nativeHeatPasses nativeGap123Old nativeHeat122Frames nativeHeat122Coef nativeHeat122Fixed nativeHeat122Base 20 nativeHeat122Y00 = nativeHeat122Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat122Pass20]
  have h24 : nativeHeatPasses nativeGap123Old nativeHeat122Frames nativeHeat122Coef nativeHeat122Fixed nativeHeat122Base 24 nativeHeat122Y00 = nativeHeat122Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat122Pass24]
  have h28 : nativeHeatPasses nativeGap123Old nativeHeat122Frames nativeHeat122Coef nativeHeat122Fixed nativeHeat122Base 28 nativeHeat122Y00 = nativeHeat122Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat122Pass28]
  have h32 : nativeHeatPasses nativeGap123Old nativeHeat122Frames nativeHeat122Coef nativeHeat122Fixed nativeHeat122Base 32 nativeHeat122Y00 = nativeHeat122Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat122Pass32]
  have h36 : nativeHeatPasses nativeGap123Old nativeHeat122Frames nativeHeat122Coef nativeHeat122Fixed nativeHeat122Base 36 nativeHeat122Y00 = nativeHeat122Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat122Pass36]
  have h40 : nativeHeatPasses nativeGap123Old nativeHeat122Frames nativeHeat122Coef nativeHeat122Fixed nativeHeat122Base 40 nativeHeat122Y00 = nativeHeat122Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat122Pass40]
  have h44 : nativeHeatPasses nativeGap123Old nativeHeat122Frames nativeHeat122Coef nativeHeat122Fixed nativeHeat122Base 44 nativeHeat122Y00 = nativeHeat122Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat122Pass44]
  have h48 : nativeHeatPasses nativeGap123Old nativeHeat122Frames nativeHeat122Coef nativeHeat122Fixed nativeHeat122Base 48 nativeHeat122Y00 = nativeHeat122Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat122Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
