module
public import ASDExplicitGamma.Numerics.Native.Heat159Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat159Y00_formula : nativeHeat159Y00 = nativeHeat159Frames.y := by
  decide +kernel

theorem nativeHeat159All48 : nativeHeatPasses nativeGap160Old nativeHeat159Frames nativeHeat159Coef nativeHeat159Fixed nativeHeat159Base 48 nativeHeat159Frames.y = nativeHeat159Y48 := by
  rw [← nativeHeat159Y00_formula]
  have h4 : nativeHeatPasses nativeGap160Old nativeHeat159Frames nativeHeat159Coef nativeHeat159Fixed nativeHeat159Base 4 nativeHeat159Y00 = nativeHeat159Y04 := nativeHeat159Pass04
  have h8 : nativeHeatPasses nativeGap160Old nativeHeat159Frames nativeHeat159Coef nativeHeat159Fixed nativeHeat159Base 8 nativeHeat159Y00 = nativeHeat159Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat159Pass08]
  have h12 : nativeHeatPasses nativeGap160Old nativeHeat159Frames nativeHeat159Coef nativeHeat159Fixed nativeHeat159Base 12 nativeHeat159Y00 = nativeHeat159Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat159Pass12]
  have h16 : nativeHeatPasses nativeGap160Old nativeHeat159Frames nativeHeat159Coef nativeHeat159Fixed nativeHeat159Base 16 nativeHeat159Y00 = nativeHeat159Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat159Pass16]
  have h20 : nativeHeatPasses nativeGap160Old nativeHeat159Frames nativeHeat159Coef nativeHeat159Fixed nativeHeat159Base 20 nativeHeat159Y00 = nativeHeat159Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat159Pass20]
  have h24 : nativeHeatPasses nativeGap160Old nativeHeat159Frames nativeHeat159Coef nativeHeat159Fixed nativeHeat159Base 24 nativeHeat159Y00 = nativeHeat159Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat159Pass24]
  have h28 : nativeHeatPasses nativeGap160Old nativeHeat159Frames nativeHeat159Coef nativeHeat159Fixed nativeHeat159Base 28 nativeHeat159Y00 = nativeHeat159Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat159Pass28]
  have h32 : nativeHeatPasses nativeGap160Old nativeHeat159Frames nativeHeat159Coef nativeHeat159Fixed nativeHeat159Base 32 nativeHeat159Y00 = nativeHeat159Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat159Pass32]
  have h36 : nativeHeatPasses nativeGap160Old nativeHeat159Frames nativeHeat159Coef nativeHeat159Fixed nativeHeat159Base 36 nativeHeat159Y00 = nativeHeat159Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat159Pass36]
  have h40 : nativeHeatPasses nativeGap160Old nativeHeat159Frames nativeHeat159Coef nativeHeat159Fixed nativeHeat159Base 40 nativeHeat159Y00 = nativeHeat159Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat159Pass40]
  have h44 : nativeHeatPasses nativeGap160Old nativeHeat159Frames nativeHeat159Coef nativeHeat159Fixed nativeHeat159Base 44 nativeHeat159Y00 = nativeHeat159Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat159Pass44]
  have h48 : nativeHeatPasses nativeGap160Old nativeHeat159Frames nativeHeat159Coef nativeHeat159Fixed nativeHeat159Base 48 nativeHeat159Y00 = nativeHeat159Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat159Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
