module
public import ASDExplicitGamma.Numerics.Native.Heat024Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat024Y00_formula : nativeHeat024Y00 = nativeHeat024Frames.y := by
  decide +kernel

theorem nativeHeat024All48 : nativeHeatPasses nativeGap025Old nativeHeat024Frames nativeHeat024Coef nativeHeat024Fixed nativeHeat024Base 48 nativeHeat024Frames.y = nativeHeat024Y48 := by
  rw [← nativeHeat024Y00_formula]
  have h4 : nativeHeatPasses nativeGap025Old nativeHeat024Frames nativeHeat024Coef nativeHeat024Fixed nativeHeat024Base 4 nativeHeat024Y00 = nativeHeat024Y04 := nativeHeat024Pass04
  have h8 : nativeHeatPasses nativeGap025Old nativeHeat024Frames nativeHeat024Coef nativeHeat024Fixed nativeHeat024Base 8 nativeHeat024Y00 = nativeHeat024Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat024Pass08]
  have h12 : nativeHeatPasses nativeGap025Old nativeHeat024Frames nativeHeat024Coef nativeHeat024Fixed nativeHeat024Base 12 nativeHeat024Y00 = nativeHeat024Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat024Pass12]
  have h16 : nativeHeatPasses nativeGap025Old nativeHeat024Frames nativeHeat024Coef nativeHeat024Fixed nativeHeat024Base 16 nativeHeat024Y00 = nativeHeat024Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat024Pass16]
  have h20 : nativeHeatPasses nativeGap025Old nativeHeat024Frames nativeHeat024Coef nativeHeat024Fixed nativeHeat024Base 20 nativeHeat024Y00 = nativeHeat024Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat024Pass20]
  have h24 : nativeHeatPasses nativeGap025Old nativeHeat024Frames nativeHeat024Coef nativeHeat024Fixed nativeHeat024Base 24 nativeHeat024Y00 = nativeHeat024Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat024Pass24]
  have h28 : nativeHeatPasses nativeGap025Old nativeHeat024Frames nativeHeat024Coef nativeHeat024Fixed nativeHeat024Base 28 nativeHeat024Y00 = nativeHeat024Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat024Pass28]
  have h32 : nativeHeatPasses nativeGap025Old nativeHeat024Frames nativeHeat024Coef nativeHeat024Fixed nativeHeat024Base 32 nativeHeat024Y00 = nativeHeat024Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat024Pass32]
  have h36 : nativeHeatPasses nativeGap025Old nativeHeat024Frames nativeHeat024Coef nativeHeat024Fixed nativeHeat024Base 36 nativeHeat024Y00 = nativeHeat024Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat024Pass36]
  have h40 : nativeHeatPasses nativeGap025Old nativeHeat024Frames nativeHeat024Coef nativeHeat024Fixed nativeHeat024Base 40 nativeHeat024Y00 = nativeHeat024Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat024Pass40]
  have h44 : nativeHeatPasses nativeGap025Old nativeHeat024Frames nativeHeat024Coef nativeHeat024Fixed nativeHeat024Base 44 nativeHeat024Y00 = nativeHeat024Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat024Pass44]
  have h48 : nativeHeatPasses nativeGap025Old nativeHeat024Frames nativeHeat024Coef nativeHeat024Fixed nativeHeat024Base 48 nativeHeat024Y00 = nativeHeat024Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat024Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
