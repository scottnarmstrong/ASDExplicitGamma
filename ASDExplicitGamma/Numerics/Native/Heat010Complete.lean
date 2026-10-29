module
public import ASDExplicitGamma.Numerics.Native.Heat010Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat010Y00_formula : nativeHeat010Y00 = nativeHeat010Frames.y := by
  decide +kernel

theorem nativeHeat010All48 : nativeHeatPasses nativeGap011Old nativeHeat010Frames nativeHeat010Coef nativeHeat010Fixed nativeHeat010Base 48 nativeHeat010Frames.y = nativeHeat010Y48 := by
  rw [← nativeHeat010Y00_formula]
  have h4 : nativeHeatPasses nativeGap011Old nativeHeat010Frames nativeHeat010Coef nativeHeat010Fixed nativeHeat010Base 4 nativeHeat010Y00 = nativeHeat010Y04 := nativeHeat010Pass04
  have h8 : nativeHeatPasses nativeGap011Old nativeHeat010Frames nativeHeat010Coef nativeHeat010Fixed nativeHeat010Base 8 nativeHeat010Y00 = nativeHeat010Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat010Pass08]
  have h12 : nativeHeatPasses nativeGap011Old nativeHeat010Frames nativeHeat010Coef nativeHeat010Fixed nativeHeat010Base 12 nativeHeat010Y00 = nativeHeat010Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat010Pass12]
  have h16 : nativeHeatPasses nativeGap011Old nativeHeat010Frames nativeHeat010Coef nativeHeat010Fixed nativeHeat010Base 16 nativeHeat010Y00 = nativeHeat010Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat010Pass16]
  have h20 : nativeHeatPasses nativeGap011Old nativeHeat010Frames nativeHeat010Coef nativeHeat010Fixed nativeHeat010Base 20 nativeHeat010Y00 = nativeHeat010Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat010Pass20]
  have h24 : nativeHeatPasses nativeGap011Old nativeHeat010Frames nativeHeat010Coef nativeHeat010Fixed nativeHeat010Base 24 nativeHeat010Y00 = nativeHeat010Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat010Pass24]
  have h28 : nativeHeatPasses nativeGap011Old nativeHeat010Frames nativeHeat010Coef nativeHeat010Fixed nativeHeat010Base 28 nativeHeat010Y00 = nativeHeat010Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat010Pass28]
  have h32 : nativeHeatPasses nativeGap011Old nativeHeat010Frames nativeHeat010Coef nativeHeat010Fixed nativeHeat010Base 32 nativeHeat010Y00 = nativeHeat010Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat010Pass32]
  have h36 : nativeHeatPasses nativeGap011Old nativeHeat010Frames nativeHeat010Coef nativeHeat010Fixed nativeHeat010Base 36 nativeHeat010Y00 = nativeHeat010Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat010Pass36]
  have h40 : nativeHeatPasses nativeGap011Old nativeHeat010Frames nativeHeat010Coef nativeHeat010Fixed nativeHeat010Base 40 nativeHeat010Y00 = nativeHeat010Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat010Pass40]
  have h44 : nativeHeatPasses nativeGap011Old nativeHeat010Frames nativeHeat010Coef nativeHeat010Fixed nativeHeat010Base 44 nativeHeat010Y00 = nativeHeat010Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat010Pass44]
  have h48 : nativeHeatPasses nativeGap011Old nativeHeat010Frames nativeHeat010Coef nativeHeat010Fixed nativeHeat010Base 48 nativeHeat010Y00 = nativeHeat010Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat010Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
