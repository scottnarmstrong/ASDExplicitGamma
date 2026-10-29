module
public import ASDExplicitGamma.Numerics.Native.Heat071Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat071Y00_formula : nativeHeat071Y00 = nativeHeat071Frames.y := by
  decide +kernel

theorem nativeHeat071All48 : nativeHeatPasses nativeGap072Old nativeHeat071Frames nativeHeat071Coef nativeHeat071Fixed nativeHeat071Base 48 nativeHeat071Frames.y = nativeHeat071Y48 := by
  rw [← nativeHeat071Y00_formula]
  have h4 : nativeHeatPasses nativeGap072Old nativeHeat071Frames nativeHeat071Coef nativeHeat071Fixed nativeHeat071Base 4 nativeHeat071Y00 = nativeHeat071Y04 := nativeHeat071Pass04
  have h8 : nativeHeatPasses nativeGap072Old nativeHeat071Frames nativeHeat071Coef nativeHeat071Fixed nativeHeat071Base 8 nativeHeat071Y00 = nativeHeat071Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat071Pass08]
  have h12 : nativeHeatPasses nativeGap072Old nativeHeat071Frames nativeHeat071Coef nativeHeat071Fixed nativeHeat071Base 12 nativeHeat071Y00 = nativeHeat071Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat071Pass12]
  have h16 : nativeHeatPasses nativeGap072Old nativeHeat071Frames nativeHeat071Coef nativeHeat071Fixed nativeHeat071Base 16 nativeHeat071Y00 = nativeHeat071Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat071Pass16]
  have h20 : nativeHeatPasses nativeGap072Old nativeHeat071Frames nativeHeat071Coef nativeHeat071Fixed nativeHeat071Base 20 nativeHeat071Y00 = nativeHeat071Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat071Pass20]
  have h24 : nativeHeatPasses nativeGap072Old nativeHeat071Frames nativeHeat071Coef nativeHeat071Fixed nativeHeat071Base 24 nativeHeat071Y00 = nativeHeat071Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat071Pass24]
  have h28 : nativeHeatPasses nativeGap072Old nativeHeat071Frames nativeHeat071Coef nativeHeat071Fixed nativeHeat071Base 28 nativeHeat071Y00 = nativeHeat071Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat071Pass28]
  have h32 : nativeHeatPasses nativeGap072Old nativeHeat071Frames nativeHeat071Coef nativeHeat071Fixed nativeHeat071Base 32 nativeHeat071Y00 = nativeHeat071Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat071Pass32]
  have h36 : nativeHeatPasses nativeGap072Old nativeHeat071Frames nativeHeat071Coef nativeHeat071Fixed nativeHeat071Base 36 nativeHeat071Y00 = nativeHeat071Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat071Pass36]
  have h40 : nativeHeatPasses nativeGap072Old nativeHeat071Frames nativeHeat071Coef nativeHeat071Fixed nativeHeat071Base 40 nativeHeat071Y00 = nativeHeat071Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat071Pass40]
  have h44 : nativeHeatPasses nativeGap072Old nativeHeat071Frames nativeHeat071Coef nativeHeat071Fixed nativeHeat071Base 44 nativeHeat071Y00 = nativeHeat071Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat071Pass44]
  have h48 : nativeHeatPasses nativeGap072Old nativeHeat071Frames nativeHeat071Coef nativeHeat071Fixed nativeHeat071Base 48 nativeHeat071Y00 = nativeHeat071Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat071Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
