module
public import ASDExplicitGamma.Numerics.Native.Heat026Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat026Y00_formula : nativeHeat026Y00 = nativeHeat026Frames.y := by
  decide +kernel

theorem nativeHeat026All48 : nativeHeatPasses nativeGap027Old nativeHeat026Frames nativeHeat026Coef nativeHeat026Fixed nativeHeat026Base 48 nativeHeat026Frames.y = nativeHeat026Y48 := by
  rw [← nativeHeat026Y00_formula]
  have h4 : nativeHeatPasses nativeGap027Old nativeHeat026Frames nativeHeat026Coef nativeHeat026Fixed nativeHeat026Base 4 nativeHeat026Y00 = nativeHeat026Y04 := nativeHeat026Pass04
  have h8 : nativeHeatPasses nativeGap027Old nativeHeat026Frames nativeHeat026Coef nativeHeat026Fixed nativeHeat026Base 8 nativeHeat026Y00 = nativeHeat026Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat026Pass08]
  have h12 : nativeHeatPasses nativeGap027Old nativeHeat026Frames nativeHeat026Coef nativeHeat026Fixed nativeHeat026Base 12 nativeHeat026Y00 = nativeHeat026Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat026Pass12]
  have h16 : nativeHeatPasses nativeGap027Old nativeHeat026Frames nativeHeat026Coef nativeHeat026Fixed nativeHeat026Base 16 nativeHeat026Y00 = nativeHeat026Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat026Pass16]
  have h20 : nativeHeatPasses nativeGap027Old nativeHeat026Frames nativeHeat026Coef nativeHeat026Fixed nativeHeat026Base 20 nativeHeat026Y00 = nativeHeat026Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat026Pass20]
  have h24 : nativeHeatPasses nativeGap027Old nativeHeat026Frames nativeHeat026Coef nativeHeat026Fixed nativeHeat026Base 24 nativeHeat026Y00 = nativeHeat026Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat026Pass24]
  have h28 : nativeHeatPasses nativeGap027Old nativeHeat026Frames nativeHeat026Coef nativeHeat026Fixed nativeHeat026Base 28 nativeHeat026Y00 = nativeHeat026Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat026Pass28]
  have h32 : nativeHeatPasses nativeGap027Old nativeHeat026Frames nativeHeat026Coef nativeHeat026Fixed nativeHeat026Base 32 nativeHeat026Y00 = nativeHeat026Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat026Pass32]
  have h36 : nativeHeatPasses nativeGap027Old nativeHeat026Frames nativeHeat026Coef nativeHeat026Fixed nativeHeat026Base 36 nativeHeat026Y00 = nativeHeat026Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat026Pass36]
  have h40 : nativeHeatPasses nativeGap027Old nativeHeat026Frames nativeHeat026Coef nativeHeat026Fixed nativeHeat026Base 40 nativeHeat026Y00 = nativeHeat026Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat026Pass40]
  have h44 : nativeHeatPasses nativeGap027Old nativeHeat026Frames nativeHeat026Coef nativeHeat026Fixed nativeHeat026Base 44 nativeHeat026Y00 = nativeHeat026Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat026Pass44]
  have h48 : nativeHeatPasses nativeGap027Old nativeHeat026Frames nativeHeat026Coef nativeHeat026Fixed nativeHeat026Base 48 nativeHeat026Y00 = nativeHeat026Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat026Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
