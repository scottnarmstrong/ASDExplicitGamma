module
public import ASDExplicitGamma.Numerics.Native.Heat041Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat041Y00_formula : nativeHeat041Y00 = nativeHeat041Frames.y := by
  decide +kernel

theorem nativeHeat041All48 : nativeHeatPasses nativeGap042Old nativeHeat041Frames nativeHeat041Coef nativeHeat041Fixed nativeHeat041Base 48 nativeHeat041Frames.y = nativeHeat041Y48 := by
  rw [← nativeHeat041Y00_formula]
  have h4 : nativeHeatPasses nativeGap042Old nativeHeat041Frames nativeHeat041Coef nativeHeat041Fixed nativeHeat041Base 4 nativeHeat041Y00 = nativeHeat041Y04 := nativeHeat041Pass04
  have h8 : nativeHeatPasses nativeGap042Old nativeHeat041Frames nativeHeat041Coef nativeHeat041Fixed nativeHeat041Base 8 nativeHeat041Y00 = nativeHeat041Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat041Pass08]
  have h12 : nativeHeatPasses nativeGap042Old nativeHeat041Frames nativeHeat041Coef nativeHeat041Fixed nativeHeat041Base 12 nativeHeat041Y00 = nativeHeat041Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat041Pass12]
  have h16 : nativeHeatPasses nativeGap042Old nativeHeat041Frames nativeHeat041Coef nativeHeat041Fixed nativeHeat041Base 16 nativeHeat041Y00 = nativeHeat041Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat041Pass16]
  have h20 : nativeHeatPasses nativeGap042Old nativeHeat041Frames nativeHeat041Coef nativeHeat041Fixed nativeHeat041Base 20 nativeHeat041Y00 = nativeHeat041Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat041Pass20]
  have h24 : nativeHeatPasses nativeGap042Old nativeHeat041Frames nativeHeat041Coef nativeHeat041Fixed nativeHeat041Base 24 nativeHeat041Y00 = nativeHeat041Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat041Pass24]
  have h28 : nativeHeatPasses nativeGap042Old nativeHeat041Frames nativeHeat041Coef nativeHeat041Fixed nativeHeat041Base 28 nativeHeat041Y00 = nativeHeat041Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat041Pass28]
  have h32 : nativeHeatPasses nativeGap042Old nativeHeat041Frames nativeHeat041Coef nativeHeat041Fixed nativeHeat041Base 32 nativeHeat041Y00 = nativeHeat041Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat041Pass32]
  have h36 : nativeHeatPasses nativeGap042Old nativeHeat041Frames nativeHeat041Coef nativeHeat041Fixed nativeHeat041Base 36 nativeHeat041Y00 = nativeHeat041Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat041Pass36]
  have h40 : nativeHeatPasses nativeGap042Old nativeHeat041Frames nativeHeat041Coef nativeHeat041Fixed nativeHeat041Base 40 nativeHeat041Y00 = nativeHeat041Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat041Pass40]
  have h44 : nativeHeatPasses nativeGap042Old nativeHeat041Frames nativeHeat041Coef nativeHeat041Fixed nativeHeat041Base 44 nativeHeat041Y00 = nativeHeat041Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat041Pass44]
  have h48 : nativeHeatPasses nativeGap042Old nativeHeat041Frames nativeHeat041Coef nativeHeat041Fixed nativeHeat041Base 48 nativeHeat041Y00 = nativeHeat041Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat041Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
