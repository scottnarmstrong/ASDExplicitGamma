module
public import ASDExplicitGamma.Numerics.Native.Heat021Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat021Y00_formula : nativeHeat021Y00 = nativeHeat021Frames.y := by
  decide +kernel

theorem nativeHeat021All48 : nativeHeatPasses nativeGap022Old nativeHeat021Frames nativeHeat021Coef nativeHeat021Fixed nativeHeat021Base 48 nativeHeat021Frames.y = nativeHeat021Y48 := by
  rw [← nativeHeat021Y00_formula]
  have h4 : nativeHeatPasses nativeGap022Old nativeHeat021Frames nativeHeat021Coef nativeHeat021Fixed nativeHeat021Base 4 nativeHeat021Y00 = nativeHeat021Y04 := nativeHeat021Pass04
  have h8 : nativeHeatPasses nativeGap022Old nativeHeat021Frames nativeHeat021Coef nativeHeat021Fixed nativeHeat021Base 8 nativeHeat021Y00 = nativeHeat021Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat021Pass08]
  have h12 : nativeHeatPasses nativeGap022Old nativeHeat021Frames nativeHeat021Coef nativeHeat021Fixed nativeHeat021Base 12 nativeHeat021Y00 = nativeHeat021Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat021Pass12]
  have h16 : nativeHeatPasses nativeGap022Old nativeHeat021Frames nativeHeat021Coef nativeHeat021Fixed nativeHeat021Base 16 nativeHeat021Y00 = nativeHeat021Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat021Pass16]
  have h20 : nativeHeatPasses nativeGap022Old nativeHeat021Frames nativeHeat021Coef nativeHeat021Fixed nativeHeat021Base 20 nativeHeat021Y00 = nativeHeat021Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat021Pass20]
  have h24 : nativeHeatPasses nativeGap022Old nativeHeat021Frames nativeHeat021Coef nativeHeat021Fixed nativeHeat021Base 24 nativeHeat021Y00 = nativeHeat021Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat021Pass24]
  have h28 : nativeHeatPasses nativeGap022Old nativeHeat021Frames nativeHeat021Coef nativeHeat021Fixed nativeHeat021Base 28 nativeHeat021Y00 = nativeHeat021Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat021Pass28]
  have h32 : nativeHeatPasses nativeGap022Old nativeHeat021Frames nativeHeat021Coef nativeHeat021Fixed nativeHeat021Base 32 nativeHeat021Y00 = nativeHeat021Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat021Pass32]
  have h36 : nativeHeatPasses nativeGap022Old nativeHeat021Frames nativeHeat021Coef nativeHeat021Fixed nativeHeat021Base 36 nativeHeat021Y00 = nativeHeat021Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat021Pass36]
  have h40 : nativeHeatPasses nativeGap022Old nativeHeat021Frames nativeHeat021Coef nativeHeat021Fixed nativeHeat021Base 40 nativeHeat021Y00 = nativeHeat021Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat021Pass40]
  have h44 : nativeHeatPasses nativeGap022Old nativeHeat021Frames nativeHeat021Coef nativeHeat021Fixed nativeHeat021Base 44 nativeHeat021Y00 = nativeHeat021Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat021Pass44]
  have h48 : nativeHeatPasses nativeGap022Old nativeHeat021Frames nativeHeat021Coef nativeHeat021Fixed nativeHeat021Base 48 nativeHeat021Y00 = nativeHeat021Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat021Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
