module
public import ASDExplicitGamma.Numerics.Native.Heat019Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat019Y00_formula : nativeHeat019Y00 = nativeHeat019Frames.y := by
  decide +kernel

theorem nativeHeat019All48 : nativeHeatPasses nativeGap020Old nativeHeat019Frames nativeHeat019Coef nativeHeat019Fixed nativeHeat019Base 48 nativeHeat019Frames.y = nativeHeat019Y48 := by
  rw [← nativeHeat019Y00_formula]
  have h4 : nativeHeatPasses nativeGap020Old nativeHeat019Frames nativeHeat019Coef nativeHeat019Fixed nativeHeat019Base 4 nativeHeat019Y00 = nativeHeat019Y04 := nativeHeat019Pass04
  have h8 : nativeHeatPasses nativeGap020Old nativeHeat019Frames nativeHeat019Coef nativeHeat019Fixed nativeHeat019Base 8 nativeHeat019Y00 = nativeHeat019Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat019Pass08]
  have h12 : nativeHeatPasses nativeGap020Old nativeHeat019Frames nativeHeat019Coef nativeHeat019Fixed nativeHeat019Base 12 nativeHeat019Y00 = nativeHeat019Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat019Pass12]
  have h16 : nativeHeatPasses nativeGap020Old nativeHeat019Frames nativeHeat019Coef nativeHeat019Fixed nativeHeat019Base 16 nativeHeat019Y00 = nativeHeat019Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat019Pass16]
  have h20 : nativeHeatPasses nativeGap020Old nativeHeat019Frames nativeHeat019Coef nativeHeat019Fixed nativeHeat019Base 20 nativeHeat019Y00 = nativeHeat019Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat019Pass20]
  have h24 : nativeHeatPasses nativeGap020Old nativeHeat019Frames nativeHeat019Coef nativeHeat019Fixed nativeHeat019Base 24 nativeHeat019Y00 = nativeHeat019Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat019Pass24]
  have h28 : nativeHeatPasses nativeGap020Old nativeHeat019Frames nativeHeat019Coef nativeHeat019Fixed nativeHeat019Base 28 nativeHeat019Y00 = nativeHeat019Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat019Pass28]
  have h32 : nativeHeatPasses nativeGap020Old nativeHeat019Frames nativeHeat019Coef nativeHeat019Fixed nativeHeat019Base 32 nativeHeat019Y00 = nativeHeat019Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat019Pass32]
  have h36 : nativeHeatPasses nativeGap020Old nativeHeat019Frames nativeHeat019Coef nativeHeat019Fixed nativeHeat019Base 36 nativeHeat019Y00 = nativeHeat019Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat019Pass36]
  have h40 : nativeHeatPasses nativeGap020Old nativeHeat019Frames nativeHeat019Coef nativeHeat019Fixed nativeHeat019Base 40 nativeHeat019Y00 = nativeHeat019Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat019Pass40]
  have h44 : nativeHeatPasses nativeGap020Old nativeHeat019Frames nativeHeat019Coef nativeHeat019Fixed nativeHeat019Base 44 nativeHeat019Y00 = nativeHeat019Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat019Pass44]
  have h48 : nativeHeatPasses nativeGap020Old nativeHeat019Frames nativeHeat019Coef nativeHeat019Fixed nativeHeat019Base 48 nativeHeat019Y00 = nativeHeat019Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat019Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
