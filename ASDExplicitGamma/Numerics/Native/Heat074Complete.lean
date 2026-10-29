module
public import ASDExplicitGamma.Numerics.Native.Heat074Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat074Y00_formula : nativeHeat074Y00 = nativeHeat074Frames.y := by
  decide +kernel

theorem nativeHeat074All48 : nativeHeatPasses nativeGap075Old nativeHeat074Frames nativeHeat074Coef nativeHeat074Fixed nativeHeat074Base 48 nativeHeat074Frames.y = nativeHeat074Y48 := by
  rw [← nativeHeat074Y00_formula]
  have h4 : nativeHeatPasses nativeGap075Old nativeHeat074Frames nativeHeat074Coef nativeHeat074Fixed nativeHeat074Base 4 nativeHeat074Y00 = nativeHeat074Y04 := nativeHeat074Pass04
  have h8 : nativeHeatPasses nativeGap075Old nativeHeat074Frames nativeHeat074Coef nativeHeat074Fixed nativeHeat074Base 8 nativeHeat074Y00 = nativeHeat074Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat074Pass08]
  have h12 : nativeHeatPasses nativeGap075Old nativeHeat074Frames nativeHeat074Coef nativeHeat074Fixed nativeHeat074Base 12 nativeHeat074Y00 = nativeHeat074Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat074Pass12]
  have h16 : nativeHeatPasses nativeGap075Old nativeHeat074Frames nativeHeat074Coef nativeHeat074Fixed nativeHeat074Base 16 nativeHeat074Y00 = nativeHeat074Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat074Pass16]
  have h20 : nativeHeatPasses nativeGap075Old nativeHeat074Frames nativeHeat074Coef nativeHeat074Fixed nativeHeat074Base 20 nativeHeat074Y00 = nativeHeat074Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat074Pass20]
  have h24 : nativeHeatPasses nativeGap075Old nativeHeat074Frames nativeHeat074Coef nativeHeat074Fixed nativeHeat074Base 24 nativeHeat074Y00 = nativeHeat074Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat074Pass24]
  have h28 : nativeHeatPasses nativeGap075Old nativeHeat074Frames nativeHeat074Coef nativeHeat074Fixed nativeHeat074Base 28 nativeHeat074Y00 = nativeHeat074Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat074Pass28]
  have h32 : nativeHeatPasses nativeGap075Old nativeHeat074Frames nativeHeat074Coef nativeHeat074Fixed nativeHeat074Base 32 nativeHeat074Y00 = nativeHeat074Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat074Pass32]
  have h36 : nativeHeatPasses nativeGap075Old nativeHeat074Frames nativeHeat074Coef nativeHeat074Fixed nativeHeat074Base 36 nativeHeat074Y00 = nativeHeat074Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat074Pass36]
  have h40 : nativeHeatPasses nativeGap075Old nativeHeat074Frames nativeHeat074Coef nativeHeat074Fixed nativeHeat074Base 40 nativeHeat074Y00 = nativeHeat074Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat074Pass40]
  have h44 : nativeHeatPasses nativeGap075Old nativeHeat074Frames nativeHeat074Coef nativeHeat074Fixed nativeHeat074Base 44 nativeHeat074Y00 = nativeHeat074Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat074Pass44]
  have h48 : nativeHeatPasses nativeGap075Old nativeHeat074Frames nativeHeat074Coef nativeHeat074Fixed nativeHeat074Base 48 nativeHeat074Y00 = nativeHeat074Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat074Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
