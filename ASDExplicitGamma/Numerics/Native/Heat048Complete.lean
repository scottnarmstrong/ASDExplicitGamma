module
public import ASDExplicitGamma.Numerics.Native.Heat048Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat048Y00_formula : nativeHeat048Y00 = nativeHeat048Frames.y := by
  decide +kernel

theorem nativeHeat048All48 : nativeHeatPasses nativeGap049Old nativeHeat048Frames nativeHeat048Coef nativeHeat048Fixed nativeHeat048Base 48 nativeHeat048Frames.y = nativeHeat048Y48 := by
  rw [← nativeHeat048Y00_formula]
  have h4 : nativeHeatPasses nativeGap049Old nativeHeat048Frames nativeHeat048Coef nativeHeat048Fixed nativeHeat048Base 4 nativeHeat048Y00 = nativeHeat048Y04 := nativeHeat048Pass04
  have h8 : nativeHeatPasses nativeGap049Old nativeHeat048Frames nativeHeat048Coef nativeHeat048Fixed nativeHeat048Base 8 nativeHeat048Y00 = nativeHeat048Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat048Pass08]
  have h12 : nativeHeatPasses nativeGap049Old nativeHeat048Frames nativeHeat048Coef nativeHeat048Fixed nativeHeat048Base 12 nativeHeat048Y00 = nativeHeat048Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat048Pass12]
  have h16 : nativeHeatPasses nativeGap049Old nativeHeat048Frames nativeHeat048Coef nativeHeat048Fixed nativeHeat048Base 16 nativeHeat048Y00 = nativeHeat048Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat048Pass16]
  have h20 : nativeHeatPasses nativeGap049Old nativeHeat048Frames nativeHeat048Coef nativeHeat048Fixed nativeHeat048Base 20 nativeHeat048Y00 = nativeHeat048Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat048Pass20]
  have h24 : nativeHeatPasses nativeGap049Old nativeHeat048Frames nativeHeat048Coef nativeHeat048Fixed nativeHeat048Base 24 nativeHeat048Y00 = nativeHeat048Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat048Pass24]
  have h28 : nativeHeatPasses nativeGap049Old nativeHeat048Frames nativeHeat048Coef nativeHeat048Fixed nativeHeat048Base 28 nativeHeat048Y00 = nativeHeat048Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat048Pass28]
  have h32 : nativeHeatPasses nativeGap049Old nativeHeat048Frames nativeHeat048Coef nativeHeat048Fixed nativeHeat048Base 32 nativeHeat048Y00 = nativeHeat048Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat048Pass32]
  have h36 : nativeHeatPasses nativeGap049Old nativeHeat048Frames nativeHeat048Coef nativeHeat048Fixed nativeHeat048Base 36 nativeHeat048Y00 = nativeHeat048Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat048Pass36]
  have h40 : nativeHeatPasses nativeGap049Old nativeHeat048Frames nativeHeat048Coef nativeHeat048Fixed nativeHeat048Base 40 nativeHeat048Y00 = nativeHeat048Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat048Pass40]
  have h44 : nativeHeatPasses nativeGap049Old nativeHeat048Frames nativeHeat048Coef nativeHeat048Fixed nativeHeat048Base 44 nativeHeat048Y00 = nativeHeat048Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat048Pass44]
  have h48 : nativeHeatPasses nativeGap049Old nativeHeat048Frames nativeHeat048Coef nativeHeat048Fixed nativeHeat048Base 48 nativeHeat048Y00 = nativeHeat048Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat048Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
