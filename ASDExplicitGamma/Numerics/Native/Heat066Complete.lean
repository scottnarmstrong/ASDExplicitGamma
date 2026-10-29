module
public import ASDExplicitGamma.Numerics.Native.Heat066Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat066Y00_formula : nativeHeat066Y00 = nativeHeat066Frames.y := by
  decide +kernel

theorem nativeHeat066All48 : nativeHeatPasses nativeGap067Old nativeHeat066Frames nativeHeat066Coef nativeHeat066Fixed nativeHeat066Base 48 nativeHeat066Frames.y = nativeHeat066Y48 := by
  rw [← nativeHeat066Y00_formula]
  have h4 : nativeHeatPasses nativeGap067Old nativeHeat066Frames nativeHeat066Coef nativeHeat066Fixed nativeHeat066Base 4 nativeHeat066Y00 = nativeHeat066Y04 := nativeHeat066Pass04
  have h8 : nativeHeatPasses nativeGap067Old nativeHeat066Frames nativeHeat066Coef nativeHeat066Fixed nativeHeat066Base 8 nativeHeat066Y00 = nativeHeat066Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat066Pass08]
  have h12 : nativeHeatPasses nativeGap067Old nativeHeat066Frames nativeHeat066Coef nativeHeat066Fixed nativeHeat066Base 12 nativeHeat066Y00 = nativeHeat066Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat066Pass12]
  have h16 : nativeHeatPasses nativeGap067Old nativeHeat066Frames nativeHeat066Coef nativeHeat066Fixed nativeHeat066Base 16 nativeHeat066Y00 = nativeHeat066Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat066Pass16]
  have h20 : nativeHeatPasses nativeGap067Old nativeHeat066Frames nativeHeat066Coef nativeHeat066Fixed nativeHeat066Base 20 nativeHeat066Y00 = nativeHeat066Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat066Pass20]
  have h24 : nativeHeatPasses nativeGap067Old nativeHeat066Frames nativeHeat066Coef nativeHeat066Fixed nativeHeat066Base 24 nativeHeat066Y00 = nativeHeat066Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat066Pass24]
  have h28 : nativeHeatPasses nativeGap067Old nativeHeat066Frames nativeHeat066Coef nativeHeat066Fixed nativeHeat066Base 28 nativeHeat066Y00 = nativeHeat066Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat066Pass28]
  have h32 : nativeHeatPasses nativeGap067Old nativeHeat066Frames nativeHeat066Coef nativeHeat066Fixed nativeHeat066Base 32 nativeHeat066Y00 = nativeHeat066Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat066Pass32]
  have h36 : nativeHeatPasses nativeGap067Old nativeHeat066Frames nativeHeat066Coef nativeHeat066Fixed nativeHeat066Base 36 nativeHeat066Y00 = nativeHeat066Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat066Pass36]
  have h40 : nativeHeatPasses nativeGap067Old nativeHeat066Frames nativeHeat066Coef nativeHeat066Fixed nativeHeat066Base 40 nativeHeat066Y00 = nativeHeat066Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat066Pass40]
  have h44 : nativeHeatPasses nativeGap067Old nativeHeat066Frames nativeHeat066Coef nativeHeat066Fixed nativeHeat066Base 44 nativeHeat066Y00 = nativeHeat066Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat066Pass44]
  have h48 : nativeHeatPasses nativeGap067Old nativeHeat066Frames nativeHeat066Coef nativeHeat066Fixed nativeHeat066Base 48 nativeHeat066Y00 = nativeHeat066Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat066Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
