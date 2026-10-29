module
public import ASDExplicitGamma.Numerics.Native.Heat109Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat109Y00_formula : nativeHeat109Y00 = nativeHeat109Frames.y := by
  decide +kernel

theorem nativeHeat109All48 : nativeHeatPasses nativeGap110Old nativeHeat109Frames nativeHeat109Coef nativeHeat109Fixed nativeHeat109Base 48 nativeHeat109Frames.y = nativeHeat109Y48 := by
  rw [← nativeHeat109Y00_formula]
  have h4 : nativeHeatPasses nativeGap110Old nativeHeat109Frames nativeHeat109Coef nativeHeat109Fixed nativeHeat109Base 4 nativeHeat109Y00 = nativeHeat109Y04 := nativeHeat109Pass04
  have h8 : nativeHeatPasses nativeGap110Old nativeHeat109Frames nativeHeat109Coef nativeHeat109Fixed nativeHeat109Base 8 nativeHeat109Y00 = nativeHeat109Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat109Pass08]
  have h12 : nativeHeatPasses nativeGap110Old nativeHeat109Frames nativeHeat109Coef nativeHeat109Fixed nativeHeat109Base 12 nativeHeat109Y00 = nativeHeat109Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat109Pass12]
  have h16 : nativeHeatPasses nativeGap110Old nativeHeat109Frames nativeHeat109Coef nativeHeat109Fixed nativeHeat109Base 16 nativeHeat109Y00 = nativeHeat109Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat109Pass16]
  have h20 : nativeHeatPasses nativeGap110Old nativeHeat109Frames nativeHeat109Coef nativeHeat109Fixed nativeHeat109Base 20 nativeHeat109Y00 = nativeHeat109Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat109Pass20]
  have h24 : nativeHeatPasses nativeGap110Old nativeHeat109Frames nativeHeat109Coef nativeHeat109Fixed nativeHeat109Base 24 nativeHeat109Y00 = nativeHeat109Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat109Pass24]
  have h28 : nativeHeatPasses nativeGap110Old nativeHeat109Frames nativeHeat109Coef nativeHeat109Fixed nativeHeat109Base 28 nativeHeat109Y00 = nativeHeat109Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat109Pass28]
  have h32 : nativeHeatPasses nativeGap110Old nativeHeat109Frames nativeHeat109Coef nativeHeat109Fixed nativeHeat109Base 32 nativeHeat109Y00 = nativeHeat109Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat109Pass32]
  have h36 : nativeHeatPasses nativeGap110Old nativeHeat109Frames nativeHeat109Coef nativeHeat109Fixed nativeHeat109Base 36 nativeHeat109Y00 = nativeHeat109Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat109Pass36]
  have h40 : nativeHeatPasses nativeGap110Old nativeHeat109Frames nativeHeat109Coef nativeHeat109Fixed nativeHeat109Base 40 nativeHeat109Y00 = nativeHeat109Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat109Pass40]
  have h44 : nativeHeatPasses nativeGap110Old nativeHeat109Frames nativeHeat109Coef nativeHeat109Fixed nativeHeat109Base 44 nativeHeat109Y00 = nativeHeat109Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat109Pass44]
  have h48 : nativeHeatPasses nativeGap110Old nativeHeat109Frames nativeHeat109Coef nativeHeat109Fixed nativeHeat109Base 48 nativeHeat109Y00 = nativeHeat109Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat109Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
