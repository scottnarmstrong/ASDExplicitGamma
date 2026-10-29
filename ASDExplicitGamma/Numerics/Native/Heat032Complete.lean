module
public import ASDExplicitGamma.Numerics.Native.Heat032Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat032Y00_formula : nativeHeat032Y00 = nativeHeat032Frames.y := by
  decide +kernel

theorem nativeHeat032All48 : nativeHeatPasses nativeGap033Old nativeHeat032Frames nativeHeat032Coef nativeHeat032Fixed nativeHeat032Base 48 nativeHeat032Frames.y = nativeHeat032Y48 := by
  rw [← nativeHeat032Y00_formula]
  have h4 : nativeHeatPasses nativeGap033Old nativeHeat032Frames nativeHeat032Coef nativeHeat032Fixed nativeHeat032Base 4 nativeHeat032Y00 = nativeHeat032Y04 := nativeHeat032Pass04
  have h8 : nativeHeatPasses nativeGap033Old nativeHeat032Frames nativeHeat032Coef nativeHeat032Fixed nativeHeat032Base 8 nativeHeat032Y00 = nativeHeat032Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat032Pass08]
  have h12 : nativeHeatPasses nativeGap033Old nativeHeat032Frames nativeHeat032Coef nativeHeat032Fixed nativeHeat032Base 12 nativeHeat032Y00 = nativeHeat032Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat032Pass12]
  have h16 : nativeHeatPasses nativeGap033Old nativeHeat032Frames nativeHeat032Coef nativeHeat032Fixed nativeHeat032Base 16 nativeHeat032Y00 = nativeHeat032Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat032Pass16]
  have h20 : nativeHeatPasses nativeGap033Old nativeHeat032Frames nativeHeat032Coef nativeHeat032Fixed nativeHeat032Base 20 nativeHeat032Y00 = nativeHeat032Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat032Pass20]
  have h24 : nativeHeatPasses nativeGap033Old nativeHeat032Frames nativeHeat032Coef nativeHeat032Fixed nativeHeat032Base 24 nativeHeat032Y00 = nativeHeat032Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat032Pass24]
  have h28 : nativeHeatPasses nativeGap033Old nativeHeat032Frames nativeHeat032Coef nativeHeat032Fixed nativeHeat032Base 28 nativeHeat032Y00 = nativeHeat032Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat032Pass28]
  have h32 : nativeHeatPasses nativeGap033Old nativeHeat032Frames nativeHeat032Coef nativeHeat032Fixed nativeHeat032Base 32 nativeHeat032Y00 = nativeHeat032Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat032Pass32]
  have h36 : nativeHeatPasses nativeGap033Old nativeHeat032Frames nativeHeat032Coef nativeHeat032Fixed nativeHeat032Base 36 nativeHeat032Y00 = nativeHeat032Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat032Pass36]
  have h40 : nativeHeatPasses nativeGap033Old nativeHeat032Frames nativeHeat032Coef nativeHeat032Fixed nativeHeat032Base 40 nativeHeat032Y00 = nativeHeat032Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat032Pass40]
  have h44 : nativeHeatPasses nativeGap033Old nativeHeat032Frames nativeHeat032Coef nativeHeat032Fixed nativeHeat032Base 44 nativeHeat032Y00 = nativeHeat032Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat032Pass44]
  have h48 : nativeHeatPasses nativeGap033Old nativeHeat032Frames nativeHeat032Coef nativeHeat032Fixed nativeHeat032Base 48 nativeHeat032Y00 = nativeHeat032Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat032Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
