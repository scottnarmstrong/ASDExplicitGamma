module
public import ASDExplicitGamma.Numerics.Native.Heat087Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat087Y00_formula : nativeHeat087Y00 = nativeHeat087Frames.y := by
  decide +kernel

theorem nativeHeat087All48 : nativeHeatPasses nativeGap088Old nativeHeat087Frames nativeHeat087Coef nativeHeat087Fixed nativeHeat087Base 48 nativeHeat087Frames.y = nativeHeat087Y48 := by
  rw [← nativeHeat087Y00_formula]
  have h4 : nativeHeatPasses nativeGap088Old nativeHeat087Frames nativeHeat087Coef nativeHeat087Fixed nativeHeat087Base 4 nativeHeat087Y00 = nativeHeat087Y04 := nativeHeat087Pass04
  have h8 : nativeHeatPasses nativeGap088Old nativeHeat087Frames nativeHeat087Coef nativeHeat087Fixed nativeHeat087Base 8 nativeHeat087Y00 = nativeHeat087Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat087Pass08]
  have h12 : nativeHeatPasses nativeGap088Old nativeHeat087Frames nativeHeat087Coef nativeHeat087Fixed nativeHeat087Base 12 nativeHeat087Y00 = nativeHeat087Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat087Pass12]
  have h16 : nativeHeatPasses nativeGap088Old nativeHeat087Frames nativeHeat087Coef nativeHeat087Fixed nativeHeat087Base 16 nativeHeat087Y00 = nativeHeat087Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat087Pass16]
  have h20 : nativeHeatPasses nativeGap088Old nativeHeat087Frames nativeHeat087Coef nativeHeat087Fixed nativeHeat087Base 20 nativeHeat087Y00 = nativeHeat087Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat087Pass20]
  have h24 : nativeHeatPasses nativeGap088Old nativeHeat087Frames nativeHeat087Coef nativeHeat087Fixed nativeHeat087Base 24 nativeHeat087Y00 = nativeHeat087Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat087Pass24]
  have h28 : nativeHeatPasses nativeGap088Old nativeHeat087Frames nativeHeat087Coef nativeHeat087Fixed nativeHeat087Base 28 nativeHeat087Y00 = nativeHeat087Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat087Pass28]
  have h32 : nativeHeatPasses nativeGap088Old nativeHeat087Frames nativeHeat087Coef nativeHeat087Fixed nativeHeat087Base 32 nativeHeat087Y00 = nativeHeat087Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat087Pass32]
  have h36 : nativeHeatPasses nativeGap088Old nativeHeat087Frames nativeHeat087Coef nativeHeat087Fixed nativeHeat087Base 36 nativeHeat087Y00 = nativeHeat087Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat087Pass36]
  have h40 : nativeHeatPasses nativeGap088Old nativeHeat087Frames nativeHeat087Coef nativeHeat087Fixed nativeHeat087Base 40 nativeHeat087Y00 = nativeHeat087Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat087Pass40]
  have h44 : nativeHeatPasses nativeGap088Old nativeHeat087Frames nativeHeat087Coef nativeHeat087Fixed nativeHeat087Base 44 nativeHeat087Y00 = nativeHeat087Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat087Pass44]
  have h48 : nativeHeatPasses nativeGap088Old nativeHeat087Frames nativeHeat087Coef nativeHeat087Fixed nativeHeat087Base 48 nativeHeat087Y00 = nativeHeat087Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat087Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
