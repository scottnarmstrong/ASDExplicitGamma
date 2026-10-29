module
public import ASDExplicitGamma.Numerics.Native.Heat151Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat151Y00_formula : nativeHeat151Y00 = nativeHeat151Frames.y := by
  decide +kernel

theorem nativeHeat151All48 : nativeHeatPasses nativeGap152Old nativeHeat151Frames nativeHeat151Coef nativeHeat151Fixed nativeHeat151Base 48 nativeHeat151Frames.y = nativeHeat151Y48 := by
  rw [← nativeHeat151Y00_formula]
  have h4 : nativeHeatPasses nativeGap152Old nativeHeat151Frames nativeHeat151Coef nativeHeat151Fixed nativeHeat151Base 4 nativeHeat151Y00 = nativeHeat151Y04 := nativeHeat151Pass04
  have h8 : nativeHeatPasses nativeGap152Old nativeHeat151Frames nativeHeat151Coef nativeHeat151Fixed nativeHeat151Base 8 nativeHeat151Y00 = nativeHeat151Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat151Pass08]
  have h12 : nativeHeatPasses nativeGap152Old nativeHeat151Frames nativeHeat151Coef nativeHeat151Fixed nativeHeat151Base 12 nativeHeat151Y00 = nativeHeat151Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat151Pass12]
  have h16 : nativeHeatPasses nativeGap152Old nativeHeat151Frames nativeHeat151Coef nativeHeat151Fixed nativeHeat151Base 16 nativeHeat151Y00 = nativeHeat151Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat151Pass16]
  have h20 : nativeHeatPasses nativeGap152Old nativeHeat151Frames nativeHeat151Coef nativeHeat151Fixed nativeHeat151Base 20 nativeHeat151Y00 = nativeHeat151Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat151Pass20]
  have h24 : nativeHeatPasses nativeGap152Old nativeHeat151Frames nativeHeat151Coef nativeHeat151Fixed nativeHeat151Base 24 nativeHeat151Y00 = nativeHeat151Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat151Pass24]
  have h28 : nativeHeatPasses nativeGap152Old nativeHeat151Frames nativeHeat151Coef nativeHeat151Fixed nativeHeat151Base 28 nativeHeat151Y00 = nativeHeat151Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat151Pass28]
  have h32 : nativeHeatPasses nativeGap152Old nativeHeat151Frames nativeHeat151Coef nativeHeat151Fixed nativeHeat151Base 32 nativeHeat151Y00 = nativeHeat151Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat151Pass32]
  have h36 : nativeHeatPasses nativeGap152Old nativeHeat151Frames nativeHeat151Coef nativeHeat151Fixed nativeHeat151Base 36 nativeHeat151Y00 = nativeHeat151Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat151Pass36]
  have h40 : nativeHeatPasses nativeGap152Old nativeHeat151Frames nativeHeat151Coef nativeHeat151Fixed nativeHeat151Base 40 nativeHeat151Y00 = nativeHeat151Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat151Pass40]
  have h44 : nativeHeatPasses nativeGap152Old nativeHeat151Frames nativeHeat151Coef nativeHeat151Fixed nativeHeat151Base 44 nativeHeat151Y00 = nativeHeat151Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat151Pass44]
  have h48 : nativeHeatPasses nativeGap152Old nativeHeat151Frames nativeHeat151Coef nativeHeat151Fixed nativeHeat151Base 48 nativeHeat151Y00 = nativeHeat151Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat151Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
