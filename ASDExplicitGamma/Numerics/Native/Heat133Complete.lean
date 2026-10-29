module
public import ASDExplicitGamma.Numerics.Native.Heat133Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat133Y00_formula : nativeHeat133Y00 = nativeHeat133Frames.y := by
  decide +kernel

theorem nativeHeat133All48 : nativeHeatPasses nativeGap134Old nativeHeat133Frames nativeHeat133Coef nativeHeat133Fixed nativeHeat133Base 48 nativeHeat133Frames.y = nativeHeat133Y48 := by
  rw [← nativeHeat133Y00_formula]
  have h4 : nativeHeatPasses nativeGap134Old nativeHeat133Frames nativeHeat133Coef nativeHeat133Fixed nativeHeat133Base 4 nativeHeat133Y00 = nativeHeat133Y04 := nativeHeat133Pass04
  have h8 : nativeHeatPasses nativeGap134Old nativeHeat133Frames nativeHeat133Coef nativeHeat133Fixed nativeHeat133Base 8 nativeHeat133Y00 = nativeHeat133Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat133Pass08]
  have h12 : nativeHeatPasses nativeGap134Old nativeHeat133Frames nativeHeat133Coef nativeHeat133Fixed nativeHeat133Base 12 nativeHeat133Y00 = nativeHeat133Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat133Pass12]
  have h16 : nativeHeatPasses nativeGap134Old nativeHeat133Frames nativeHeat133Coef nativeHeat133Fixed nativeHeat133Base 16 nativeHeat133Y00 = nativeHeat133Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat133Pass16]
  have h20 : nativeHeatPasses nativeGap134Old nativeHeat133Frames nativeHeat133Coef nativeHeat133Fixed nativeHeat133Base 20 nativeHeat133Y00 = nativeHeat133Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat133Pass20]
  have h24 : nativeHeatPasses nativeGap134Old nativeHeat133Frames nativeHeat133Coef nativeHeat133Fixed nativeHeat133Base 24 nativeHeat133Y00 = nativeHeat133Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat133Pass24]
  have h28 : nativeHeatPasses nativeGap134Old nativeHeat133Frames nativeHeat133Coef nativeHeat133Fixed nativeHeat133Base 28 nativeHeat133Y00 = nativeHeat133Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat133Pass28]
  have h32 : nativeHeatPasses nativeGap134Old nativeHeat133Frames nativeHeat133Coef nativeHeat133Fixed nativeHeat133Base 32 nativeHeat133Y00 = nativeHeat133Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat133Pass32]
  have h36 : nativeHeatPasses nativeGap134Old nativeHeat133Frames nativeHeat133Coef nativeHeat133Fixed nativeHeat133Base 36 nativeHeat133Y00 = nativeHeat133Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat133Pass36]
  have h40 : nativeHeatPasses nativeGap134Old nativeHeat133Frames nativeHeat133Coef nativeHeat133Fixed nativeHeat133Base 40 nativeHeat133Y00 = nativeHeat133Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat133Pass40]
  have h44 : nativeHeatPasses nativeGap134Old nativeHeat133Frames nativeHeat133Coef nativeHeat133Fixed nativeHeat133Base 44 nativeHeat133Y00 = nativeHeat133Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat133Pass44]
  have h48 : nativeHeatPasses nativeGap134Old nativeHeat133Frames nativeHeat133Coef nativeHeat133Fixed nativeHeat133Base 48 nativeHeat133Y00 = nativeHeat133Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat133Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
