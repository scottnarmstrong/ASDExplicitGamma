module
public import ASDExplicitGamma.Numerics.Native.Heat062Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat062Y00_formula : nativeHeat062Y00 = nativeHeat062Frames.y := by
  decide +kernel

theorem nativeHeat062All48 : nativeHeatPasses nativeGap063Old nativeHeat062Frames nativeHeat062Coef nativeHeat062Fixed nativeHeat062Base 48 nativeHeat062Frames.y = nativeHeat062Y48 := by
  rw [← nativeHeat062Y00_formula]
  have h4 : nativeHeatPasses nativeGap063Old nativeHeat062Frames nativeHeat062Coef nativeHeat062Fixed nativeHeat062Base 4 nativeHeat062Y00 = nativeHeat062Y04 := nativeHeat062Pass04
  have h8 : nativeHeatPasses nativeGap063Old nativeHeat062Frames nativeHeat062Coef nativeHeat062Fixed nativeHeat062Base 8 nativeHeat062Y00 = nativeHeat062Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat062Pass08]
  have h12 : nativeHeatPasses nativeGap063Old nativeHeat062Frames nativeHeat062Coef nativeHeat062Fixed nativeHeat062Base 12 nativeHeat062Y00 = nativeHeat062Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat062Pass12]
  have h16 : nativeHeatPasses nativeGap063Old nativeHeat062Frames nativeHeat062Coef nativeHeat062Fixed nativeHeat062Base 16 nativeHeat062Y00 = nativeHeat062Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat062Pass16]
  have h20 : nativeHeatPasses nativeGap063Old nativeHeat062Frames nativeHeat062Coef nativeHeat062Fixed nativeHeat062Base 20 nativeHeat062Y00 = nativeHeat062Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat062Pass20]
  have h24 : nativeHeatPasses nativeGap063Old nativeHeat062Frames nativeHeat062Coef nativeHeat062Fixed nativeHeat062Base 24 nativeHeat062Y00 = nativeHeat062Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat062Pass24]
  have h28 : nativeHeatPasses nativeGap063Old nativeHeat062Frames nativeHeat062Coef nativeHeat062Fixed nativeHeat062Base 28 nativeHeat062Y00 = nativeHeat062Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat062Pass28]
  have h32 : nativeHeatPasses nativeGap063Old nativeHeat062Frames nativeHeat062Coef nativeHeat062Fixed nativeHeat062Base 32 nativeHeat062Y00 = nativeHeat062Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat062Pass32]
  have h36 : nativeHeatPasses nativeGap063Old nativeHeat062Frames nativeHeat062Coef nativeHeat062Fixed nativeHeat062Base 36 nativeHeat062Y00 = nativeHeat062Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat062Pass36]
  have h40 : nativeHeatPasses nativeGap063Old nativeHeat062Frames nativeHeat062Coef nativeHeat062Fixed nativeHeat062Base 40 nativeHeat062Y00 = nativeHeat062Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat062Pass40]
  have h44 : nativeHeatPasses nativeGap063Old nativeHeat062Frames nativeHeat062Coef nativeHeat062Fixed nativeHeat062Base 44 nativeHeat062Y00 = nativeHeat062Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat062Pass44]
  have h48 : nativeHeatPasses nativeGap063Old nativeHeat062Frames nativeHeat062Coef nativeHeat062Fixed nativeHeat062Base 48 nativeHeat062Y00 = nativeHeat062Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat062Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
