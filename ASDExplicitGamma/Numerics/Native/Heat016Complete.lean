module
public import ASDExplicitGamma.Numerics.Native.Heat016Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat016Y00_formula : nativeHeat016Y00 = nativeHeat016Frames.y := by
  decide +kernel

theorem nativeHeat016All48 : nativeHeatPasses nativeGap017Old nativeHeat016Frames nativeHeat016Coef nativeHeat016Fixed nativeHeat016Base 48 nativeHeat016Frames.y = nativeHeat016Y48 := by
  rw [← nativeHeat016Y00_formula]
  have h4 : nativeHeatPasses nativeGap017Old nativeHeat016Frames nativeHeat016Coef nativeHeat016Fixed nativeHeat016Base 4 nativeHeat016Y00 = nativeHeat016Y04 := nativeHeat016Pass04
  have h8 : nativeHeatPasses nativeGap017Old nativeHeat016Frames nativeHeat016Coef nativeHeat016Fixed nativeHeat016Base 8 nativeHeat016Y00 = nativeHeat016Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat016Pass08]
  have h12 : nativeHeatPasses nativeGap017Old nativeHeat016Frames nativeHeat016Coef nativeHeat016Fixed nativeHeat016Base 12 nativeHeat016Y00 = nativeHeat016Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat016Pass12]
  have h16 : nativeHeatPasses nativeGap017Old nativeHeat016Frames nativeHeat016Coef nativeHeat016Fixed nativeHeat016Base 16 nativeHeat016Y00 = nativeHeat016Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat016Pass16]
  have h20 : nativeHeatPasses nativeGap017Old nativeHeat016Frames nativeHeat016Coef nativeHeat016Fixed nativeHeat016Base 20 nativeHeat016Y00 = nativeHeat016Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat016Pass20]
  have h24 : nativeHeatPasses nativeGap017Old nativeHeat016Frames nativeHeat016Coef nativeHeat016Fixed nativeHeat016Base 24 nativeHeat016Y00 = nativeHeat016Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat016Pass24]
  have h28 : nativeHeatPasses nativeGap017Old nativeHeat016Frames nativeHeat016Coef nativeHeat016Fixed nativeHeat016Base 28 nativeHeat016Y00 = nativeHeat016Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat016Pass28]
  have h32 : nativeHeatPasses nativeGap017Old nativeHeat016Frames nativeHeat016Coef nativeHeat016Fixed nativeHeat016Base 32 nativeHeat016Y00 = nativeHeat016Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat016Pass32]
  have h36 : nativeHeatPasses nativeGap017Old nativeHeat016Frames nativeHeat016Coef nativeHeat016Fixed nativeHeat016Base 36 nativeHeat016Y00 = nativeHeat016Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat016Pass36]
  have h40 : nativeHeatPasses nativeGap017Old nativeHeat016Frames nativeHeat016Coef nativeHeat016Fixed nativeHeat016Base 40 nativeHeat016Y00 = nativeHeat016Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat016Pass40]
  have h44 : nativeHeatPasses nativeGap017Old nativeHeat016Frames nativeHeat016Coef nativeHeat016Fixed nativeHeat016Base 44 nativeHeat016Y00 = nativeHeat016Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat016Pass44]
  have h48 : nativeHeatPasses nativeGap017Old nativeHeat016Frames nativeHeat016Coef nativeHeat016Fixed nativeHeat016Base 48 nativeHeat016Y00 = nativeHeat016Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat016Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
