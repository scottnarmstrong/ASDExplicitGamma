module
public import ASDExplicitGamma.Numerics.Native.Heat060Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat060Y00_formula : nativeHeat060Y00 = nativeHeat060Frames.y := by
  decide +kernel

theorem nativeHeat060All48 : nativeHeatPasses nativeGap061Old nativeHeat060Frames nativeHeat060Coef nativeHeat060Fixed nativeHeat060Base 48 nativeHeat060Frames.y = nativeHeat060Y48 := by
  rw [← nativeHeat060Y00_formula]
  have h4 : nativeHeatPasses nativeGap061Old nativeHeat060Frames nativeHeat060Coef nativeHeat060Fixed nativeHeat060Base 4 nativeHeat060Y00 = nativeHeat060Y04 := nativeHeat060Pass04
  have h8 : nativeHeatPasses nativeGap061Old nativeHeat060Frames nativeHeat060Coef nativeHeat060Fixed nativeHeat060Base 8 nativeHeat060Y00 = nativeHeat060Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat060Pass08]
  have h12 : nativeHeatPasses nativeGap061Old nativeHeat060Frames nativeHeat060Coef nativeHeat060Fixed nativeHeat060Base 12 nativeHeat060Y00 = nativeHeat060Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat060Pass12]
  have h16 : nativeHeatPasses nativeGap061Old nativeHeat060Frames nativeHeat060Coef nativeHeat060Fixed nativeHeat060Base 16 nativeHeat060Y00 = nativeHeat060Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat060Pass16]
  have h20 : nativeHeatPasses nativeGap061Old nativeHeat060Frames nativeHeat060Coef nativeHeat060Fixed nativeHeat060Base 20 nativeHeat060Y00 = nativeHeat060Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat060Pass20]
  have h24 : nativeHeatPasses nativeGap061Old nativeHeat060Frames nativeHeat060Coef nativeHeat060Fixed nativeHeat060Base 24 nativeHeat060Y00 = nativeHeat060Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat060Pass24]
  have h28 : nativeHeatPasses nativeGap061Old nativeHeat060Frames nativeHeat060Coef nativeHeat060Fixed nativeHeat060Base 28 nativeHeat060Y00 = nativeHeat060Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat060Pass28]
  have h32 : nativeHeatPasses nativeGap061Old nativeHeat060Frames nativeHeat060Coef nativeHeat060Fixed nativeHeat060Base 32 nativeHeat060Y00 = nativeHeat060Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat060Pass32]
  have h36 : nativeHeatPasses nativeGap061Old nativeHeat060Frames nativeHeat060Coef nativeHeat060Fixed nativeHeat060Base 36 nativeHeat060Y00 = nativeHeat060Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat060Pass36]
  have h40 : nativeHeatPasses nativeGap061Old nativeHeat060Frames nativeHeat060Coef nativeHeat060Fixed nativeHeat060Base 40 nativeHeat060Y00 = nativeHeat060Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat060Pass40]
  have h44 : nativeHeatPasses nativeGap061Old nativeHeat060Frames nativeHeat060Coef nativeHeat060Fixed nativeHeat060Base 44 nativeHeat060Y00 = nativeHeat060Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat060Pass44]
  have h48 : nativeHeatPasses nativeGap061Old nativeHeat060Frames nativeHeat060Coef nativeHeat060Fixed nativeHeat060Base 48 nativeHeat060Y00 = nativeHeat060Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat060Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
