module
public import ASDExplicitGamma.Numerics.Native.Heat058Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat058Y00_formula : nativeHeat058Y00 = nativeHeat058Frames.y := by
  decide +kernel

theorem nativeHeat058All48 : nativeHeatPasses nativeGap059Old nativeHeat058Frames nativeHeat058Coef nativeHeat058Fixed nativeHeat058Base 48 nativeHeat058Frames.y = nativeHeat058Y48 := by
  rw [← nativeHeat058Y00_formula]
  have h4 : nativeHeatPasses nativeGap059Old nativeHeat058Frames nativeHeat058Coef nativeHeat058Fixed nativeHeat058Base 4 nativeHeat058Y00 = nativeHeat058Y04 := nativeHeat058Pass04
  have h8 : nativeHeatPasses nativeGap059Old nativeHeat058Frames nativeHeat058Coef nativeHeat058Fixed nativeHeat058Base 8 nativeHeat058Y00 = nativeHeat058Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat058Pass08]
  have h12 : nativeHeatPasses nativeGap059Old nativeHeat058Frames nativeHeat058Coef nativeHeat058Fixed nativeHeat058Base 12 nativeHeat058Y00 = nativeHeat058Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat058Pass12]
  have h16 : nativeHeatPasses nativeGap059Old nativeHeat058Frames nativeHeat058Coef nativeHeat058Fixed nativeHeat058Base 16 nativeHeat058Y00 = nativeHeat058Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat058Pass16]
  have h20 : nativeHeatPasses nativeGap059Old nativeHeat058Frames nativeHeat058Coef nativeHeat058Fixed nativeHeat058Base 20 nativeHeat058Y00 = nativeHeat058Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat058Pass20]
  have h24 : nativeHeatPasses nativeGap059Old nativeHeat058Frames nativeHeat058Coef nativeHeat058Fixed nativeHeat058Base 24 nativeHeat058Y00 = nativeHeat058Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat058Pass24]
  have h28 : nativeHeatPasses nativeGap059Old nativeHeat058Frames nativeHeat058Coef nativeHeat058Fixed nativeHeat058Base 28 nativeHeat058Y00 = nativeHeat058Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat058Pass28]
  have h32 : nativeHeatPasses nativeGap059Old nativeHeat058Frames nativeHeat058Coef nativeHeat058Fixed nativeHeat058Base 32 nativeHeat058Y00 = nativeHeat058Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat058Pass32]
  have h36 : nativeHeatPasses nativeGap059Old nativeHeat058Frames nativeHeat058Coef nativeHeat058Fixed nativeHeat058Base 36 nativeHeat058Y00 = nativeHeat058Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat058Pass36]
  have h40 : nativeHeatPasses nativeGap059Old nativeHeat058Frames nativeHeat058Coef nativeHeat058Fixed nativeHeat058Base 40 nativeHeat058Y00 = nativeHeat058Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat058Pass40]
  have h44 : nativeHeatPasses nativeGap059Old nativeHeat058Frames nativeHeat058Coef nativeHeat058Fixed nativeHeat058Base 44 nativeHeat058Y00 = nativeHeat058Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat058Pass44]
  have h48 : nativeHeatPasses nativeGap059Old nativeHeat058Frames nativeHeat058Coef nativeHeat058Fixed nativeHeat058Base 48 nativeHeat058Y00 = nativeHeat058Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat058Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
