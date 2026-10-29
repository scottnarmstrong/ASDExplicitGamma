module
public import ASDExplicitGamma.Numerics.Native.Heat134Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat134Y00_formula : nativeHeat134Y00 = nativeHeat134Frames.y := by
  decide +kernel

theorem nativeHeat134All48 : nativeHeatPasses nativeGap135Old nativeHeat134Frames nativeHeat134Coef nativeHeat134Fixed nativeHeat134Base 48 nativeHeat134Frames.y = nativeHeat134Y48 := by
  rw [← nativeHeat134Y00_formula]
  have h4 : nativeHeatPasses nativeGap135Old nativeHeat134Frames nativeHeat134Coef nativeHeat134Fixed nativeHeat134Base 4 nativeHeat134Y00 = nativeHeat134Y04 := nativeHeat134Pass04
  have h8 : nativeHeatPasses nativeGap135Old nativeHeat134Frames nativeHeat134Coef nativeHeat134Fixed nativeHeat134Base 8 nativeHeat134Y00 = nativeHeat134Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat134Pass08]
  have h12 : nativeHeatPasses nativeGap135Old nativeHeat134Frames nativeHeat134Coef nativeHeat134Fixed nativeHeat134Base 12 nativeHeat134Y00 = nativeHeat134Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat134Pass12]
  have h16 : nativeHeatPasses nativeGap135Old nativeHeat134Frames nativeHeat134Coef nativeHeat134Fixed nativeHeat134Base 16 nativeHeat134Y00 = nativeHeat134Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat134Pass16]
  have h20 : nativeHeatPasses nativeGap135Old nativeHeat134Frames nativeHeat134Coef nativeHeat134Fixed nativeHeat134Base 20 nativeHeat134Y00 = nativeHeat134Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat134Pass20]
  have h24 : nativeHeatPasses nativeGap135Old nativeHeat134Frames nativeHeat134Coef nativeHeat134Fixed nativeHeat134Base 24 nativeHeat134Y00 = nativeHeat134Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat134Pass24]
  have h28 : nativeHeatPasses nativeGap135Old nativeHeat134Frames nativeHeat134Coef nativeHeat134Fixed nativeHeat134Base 28 nativeHeat134Y00 = nativeHeat134Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat134Pass28]
  have h32 : nativeHeatPasses nativeGap135Old nativeHeat134Frames nativeHeat134Coef nativeHeat134Fixed nativeHeat134Base 32 nativeHeat134Y00 = nativeHeat134Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat134Pass32]
  have h36 : nativeHeatPasses nativeGap135Old nativeHeat134Frames nativeHeat134Coef nativeHeat134Fixed nativeHeat134Base 36 nativeHeat134Y00 = nativeHeat134Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat134Pass36]
  have h40 : nativeHeatPasses nativeGap135Old nativeHeat134Frames nativeHeat134Coef nativeHeat134Fixed nativeHeat134Base 40 nativeHeat134Y00 = nativeHeat134Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat134Pass40]
  have h44 : nativeHeatPasses nativeGap135Old nativeHeat134Frames nativeHeat134Coef nativeHeat134Fixed nativeHeat134Base 44 nativeHeat134Y00 = nativeHeat134Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat134Pass44]
  have h48 : nativeHeatPasses nativeGap135Old nativeHeat134Frames nativeHeat134Coef nativeHeat134Fixed nativeHeat134Base 48 nativeHeat134Y00 = nativeHeat134Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat134Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
