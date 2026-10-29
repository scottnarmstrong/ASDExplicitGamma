module
public import ASDExplicitGamma.Numerics.Native.Heat049Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat049Y00_formula : nativeHeat049Y00 = nativeHeat049Frames.y := by
  decide +kernel

theorem nativeHeat049All48 : nativeHeatPasses nativeGap050Old nativeHeat049Frames nativeHeat049Coef nativeHeat049Fixed nativeHeat049Base 48 nativeHeat049Frames.y = nativeHeat049Y48 := by
  rw [← nativeHeat049Y00_formula]
  have h4 : nativeHeatPasses nativeGap050Old nativeHeat049Frames nativeHeat049Coef nativeHeat049Fixed nativeHeat049Base 4 nativeHeat049Y00 = nativeHeat049Y04 := nativeHeat049Pass04
  have h8 : nativeHeatPasses nativeGap050Old nativeHeat049Frames nativeHeat049Coef nativeHeat049Fixed nativeHeat049Base 8 nativeHeat049Y00 = nativeHeat049Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat049Pass08]
  have h12 : nativeHeatPasses nativeGap050Old nativeHeat049Frames nativeHeat049Coef nativeHeat049Fixed nativeHeat049Base 12 nativeHeat049Y00 = nativeHeat049Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat049Pass12]
  have h16 : nativeHeatPasses nativeGap050Old nativeHeat049Frames nativeHeat049Coef nativeHeat049Fixed nativeHeat049Base 16 nativeHeat049Y00 = nativeHeat049Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat049Pass16]
  have h20 : nativeHeatPasses nativeGap050Old nativeHeat049Frames nativeHeat049Coef nativeHeat049Fixed nativeHeat049Base 20 nativeHeat049Y00 = nativeHeat049Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat049Pass20]
  have h24 : nativeHeatPasses nativeGap050Old nativeHeat049Frames nativeHeat049Coef nativeHeat049Fixed nativeHeat049Base 24 nativeHeat049Y00 = nativeHeat049Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat049Pass24]
  have h28 : nativeHeatPasses nativeGap050Old nativeHeat049Frames nativeHeat049Coef nativeHeat049Fixed nativeHeat049Base 28 nativeHeat049Y00 = nativeHeat049Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat049Pass28]
  have h32 : nativeHeatPasses nativeGap050Old nativeHeat049Frames nativeHeat049Coef nativeHeat049Fixed nativeHeat049Base 32 nativeHeat049Y00 = nativeHeat049Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat049Pass32]
  have h36 : nativeHeatPasses nativeGap050Old nativeHeat049Frames nativeHeat049Coef nativeHeat049Fixed nativeHeat049Base 36 nativeHeat049Y00 = nativeHeat049Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat049Pass36]
  have h40 : nativeHeatPasses nativeGap050Old nativeHeat049Frames nativeHeat049Coef nativeHeat049Fixed nativeHeat049Base 40 nativeHeat049Y00 = nativeHeat049Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat049Pass40]
  have h44 : nativeHeatPasses nativeGap050Old nativeHeat049Frames nativeHeat049Coef nativeHeat049Fixed nativeHeat049Base 44 nativeHeat049Y00 = nativeHeat049Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat049Pass44]
  have h48 : nativeHeatPasses nativeGap050Old nativeHeat049Frames nativeHeat049Coef nativeHeat049Fixed nativeHeat049Base 48 nativeHeat049Y00 = nativeHeat049Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat049Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
