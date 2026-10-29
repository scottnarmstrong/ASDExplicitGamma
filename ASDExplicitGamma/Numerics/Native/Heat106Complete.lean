module
public import ASDExplicitGamma.Numerics.Native.Heat106Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat106Y00_formula : nativeHeat106Y00 = nativeHeat106Frames.y := by
  decide +kernel

theorem nativeHeat106All48 : nativeHeatPasses nativeGap107Old nativeHeat106Frames nativeHeat106Coef nativeHeat106Fixed nativeHeat106Base 48 nativeHeat106Frames.y = nativeHeat106Y48 := by
  rw [← nativeHeat106Y00_formula]
  have h4 : nativeHeatPasses nativeGap107Old nativeHeat106Frames nativeHeat106Coef nativeHeat106Fixed nativeHeat106Base 4 nativeHeat106Y00 = nativeHeat106Y04 := nativeHeat106Pass04
  have h8 : nativeHeatPasses nativeGap107Old nativeHeat106Frames nativeHeat106Coef nativeHeat106Fixed nativeHeat106Base 8 nativeHeat106Y00 = nativeHeat106Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat106Pass08]
  have h12 : nativeHeatPasses nativeGap107Old nativeHeat106Frames nativeHeat106Coef nativeHeat106Fixed nativeHeat106Base 12 nativeHeat106Y00 = nativeHeat106Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat106Pass12]
  have h16 : nativeHeatPasses nativeGap107Old nativeHeat106Frames nativeHeat106Coef nativeHeat106Fixed nativeHeat106Base 16 nativeHeat106Y00 = nativeHeat106Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat106Pass16]
  have h20 : nativeHeatPasses nativeGap107Old nativeHeat106Frames nativeHeat106Coef nativeHeat106Fixed nativeHeat106Base 20 nativeHeat106Y00 = nativeHeat106Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat106Pass20]
  have h24 : nativeHeatPasses nativeGap107Old nativeHeat106Frames nativeHeat106Coef nativeHeat106Fixed nativeHeat106Base 24 nativeHeat106Y00 = nativeHeat106Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat106Pass24]
  have h28 : nativeHeatPasses nativeGap107Old nativeHeat106Frames nativeHeat106Coef nativeHeat106Fixed nativeHeat106Base 28 nativeHeat106Y00 = nativeHeat106Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat106Pass28]
  have h32 : nativeHeatPasses nativeGap107Old nativeHeat106Frames nativeHeat106Coef nativeHeat106Fixed nativeHeat106Base 32 nativeHeat106Y00 = nativeHeat106Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat106Pass32]
  have h36 : nativeHeatPasses nativeGap107Old nativeHeat106Frames nativeHeat106Coef nativeHeat106Fixed nativeHeat106Base 36 nativeHeat106Y00 = nativeHeat106Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat106Pass36]
  have h40 : nativeHeatPasses nativeGap107Old nativeHeat106Frames nativeHeat106Coef nativeHeat106Fixed nativeHeat106Base 40 nativeHeat106Y00 = nativeHeat106Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat106Pass40]
  have h44 : nativeHeatPasses nativeGap107Old nativeHeat106Frames nativeHeat106Coef nativeHeat106Fixed nativeHeat106Base 44 nativeHeat106Y00 = nativeHeat106Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat106Pass44]
  have h48 : nativeHeatPasses nativeGap107Old nativeHeat106Frames nativeHeat106Coef nativeHeat106Fixed nativeHeat106Base 48 nativeHeat106Y00 = nativeHeat106Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat106Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
