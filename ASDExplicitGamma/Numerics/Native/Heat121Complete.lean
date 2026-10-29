module
public import ASDExplicitGamma.Numerics.Native.Heat121Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat121Y00_formula : nativeHeat121Y00 = nativeHeat121Frames.y := by
  decide +kernel

theorem nativeHeat121All48 : nativeHeatPasses nativeGap122Old nativeHeat121Frames nativeHeat121Coef nativeHeat121Fixed nativeHeat121Base 48 nativeHeat121Frames.y = nativeHeat121Y48 := by
  rw [← nativeHeat121Y00_formula]
  have h4 : nativeHeatPasses nativeGap122Old nativeHeat121Frames nativeHeat121Coef nativeHeat121Fixed nativeHeat121Base 4 nativeHeat121Y00 = nativeHeat121Y04 := nativeHeat121Pass04
  have h8 : nativeHeatPasses nativeGap122Old nativeHeat121Frames nativeHeat121Coef nativeHeat121Fixed nativeHeat121Base 8 nativeHeat121Y00 = nativeHeat121Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat121Pass08]
  have h12 : nativeHeatPasses nativeGap122Old nativeHeat121Frames nativeHeat121Coef nativeHeat121Fixed nativeHeat121Base 12 nativeHeat121Y00 = nativeHeat121Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat121Pass12]
  have h16 : nativeHeatPasses nativeGap122Old nativeHeat121Frames nativeHeat121Coef nativeHeat121Fixed nativeHeat121Base 16 nativeHeat121Y00 = nativeHeat121Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat121Pass16]
  have h20 : nativeHeatPasses nativeGap122Old nativeHeat121Frames nativeHeat121Coef nativeHeat121Fixed nativeHeat121Base 20 nativeHeat121Y00 = nativeHeat121Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat121Pass20]
  have h24 : nativeHeatPasses nativeGap122Old nativeHeat121Frames nativeHeat121Coef nativeHeat121Fixed nativeHeat121Base 24 nativeHeat121Y00 = nativeHeat121Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat121Pass24]
  have h28 : nativeHeatPasses nativeGap122Old nativeHeat121Frames nativeHeat121Coef nativeHeat121Fixed nativeHeat121Base 28 nativeHeat121Y00 = nativeHeat121Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat121Pass28]
  have h32 : nativeHeatPasses nativeGap122Old nativeHeat121Frames nativeHeat121Coef nativeHeat121Fixed nativeHeat121Base 32 nativeHeat121Y00 = nativeHeat121Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat121Pass32]
  have h36 : nativeHeatPasses nativeGap122Old nativeHeat121Frames nativeHeat121Coef nativeHeat121Fixed nativeHeat121Base 36 nativeHeat121Y00 = nativeHeat121Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat121Pass36]
  have h40 : nativeHeatPasses nativeGap122Old nativeHeat121Frames nativeHeat121Coef nativeHeat121Fixed nativeHeat121Base 40 nativeHeat121Y00 = nativeHeat121Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat121Pass40]
  have h44 : nativeHeatPasses nativeGap122Old nativeHeat121Frames nativeHeat121Coef nativeHeat121Fixed nativeHeat121Base 44 nativeHeat121Y00 = nativeHeat121Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat121Pass44]
  have h48 : nativeHeatPasses nativeGap122Old nativeHeat121Frames nativeHeat121Coef nativeHeat121Fixed nativeHeat121Base 48 nativeHeat121Y00 = nativeHeat121Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat121Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
