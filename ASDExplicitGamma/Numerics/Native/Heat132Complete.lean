module
public import ASDExplicitGamma.Numerics.Native.Heat132Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat132Y00_formula : nativeHeat132Y00 = nativeHeat132Frames.y := by
  decide +kernel

theorem nativeHeat132All48 : nativeHeatPasses nativeGap133Old nativeHeat132Frames nativeHeat132Coef nativeHeat132Fixed nativeHeat132Base 48 nativeHeat132Frames.y = nativeHeat132Y48 := by
  rw [← nativeHeat132Y00_formula]
  have h4 : nativeHeatPasses nativeGap133Old nativeHeat132Frames nativeHeat132Coef nativeHeat132Fixed nativeHeat132Base 4 nativeHeat132Y00 = nativeHeat132Y04 := nativeHeat132Pass04
  have h8 : nativeHeatPasses nativeGap133Old nativeHeat132Frames nativeHeat132Coef nativeHeat132Fixed nativeHeat132Base 8 nativeHeat132Y00 = nativeHeat132Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat132Pass08]
  have h12 : nativeHeatPasses nativeGap133Old nativeHeat132Frames nativeHeat132Coef nativeHeat132Fixed nativeHeat132Base 12 nativeHeat132Y00 = nativeHeat132Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat132Pass12]
  have h16 : nativeHeatPasses nativeGap133Old nativeHeat132Frames nativeHeat132Coef nativeHeat132Fixed nativeHeat132Base 16 nativeHeat132Y00 = nativeHeat132Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat132Pass16]
  have h20 : nativeHeatPasses nativeGap133Old nativeHeat132Frames nativeHeat132Coef nativeHeat132Fixed nativeHeat132Base 20 nativeHeat132Y00 = nativeHeat132Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat132Pass20]
  have h24 : nativeHeatPasses nativeGap133Old nativeHeat132Frames nativeHeat132Coef nativeHeat132Fixed nativeHeat132Base 24 nativeHeat132Y00 = nativeHeat132Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat132Pass24]
  have h28 : nativeHeatPasses nativeGap133Old nativeHeat132Frames nativeHeat132Coef nativeHeat132Fixed nativeHeat132Base 28 nativeHeat132Y00 = nativeHeat132Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat132Pass28]
  have h32 : nativeHeatPasses nativeGap133Old nativeHeat132Frames nativeHeat132Coef nativeHeat132Fixed nativeHeat132Base 32 nativeHeat132Y00 = nativeHeat132Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat132Pass32]
  have h36 : nativeHeatPasses nativeGap133Old nativeHeat132Frames nativeHeat132Coef nativeHeat132Fixed nativeHeat132Base 36 nativeHeat132Y00 = nativeHeat132Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat132Pass36]
  have h40 : nativeHeatPasses nativeGap133Old nativeHeat132Frames nativeHeat132Coef nativeHeat132Fixed nativeHeat132Base 40 nativeHeat132Y00 = nativeHeat132Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat132Pass40]
  have h44 : nativeHeatPasses nativeGap133Old nativeHeat132Frames nativeHeat132Coef nativeHeat132Fixed nativeHeat132Base 44 nativeHeat132Y00 = nativeHeat132Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat132Pass44]
  have h48 : nativeHeatPasses nativeGap133Old nativeHeat132Frames nativeHeat132Coef nativeHeat132Fixed nativeHeat132Base 48 nativeHeat132Y00 = nativeHeat132Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat132Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
