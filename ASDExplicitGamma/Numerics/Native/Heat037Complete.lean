module
public import ASDExplicitGamma.Numerics.Native.Heat037Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat037Y00_formula : nativeHeat037Y00 = nativeHeat037Frames.y := by
  decide +kernel

theorem nativeHeat037All48 : nativeHeatPasses nativeGap038Old nativeHeat037Frames nativeHeat037Coef nativeHeat037Fixed nativeHeat037Base 48 nativeHeat037Frames.y = nativeHeat037Y48 := by
  rw [← nativeHeat037Y00_formula]
  have h4 : nativeHeatPasses nativeGap038Old nativeHeat037Frames nativeHeat037Coef nativeHeat037Fixed nativeHeat037Base 4 nativeHeat037Y00 = nativeHeat037Y04 := nativeHeat037Pass04
  have h8 : nativeHeatPasses nativeGap038Old nativeHeat037Frames nativeHeat037Coef nativeHeat037Fixed nativeHeat037Base 8 nativeHeat037Y00 = nativeHeat037Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat037Pass08]
  have h12 : nativeHeatPasses nativeGap038Old nativeHeat037Frames nativeHeat037Coef nativeHeat037Fixed nativeHeat037Base 12 nativeHeat037Y00 = nativeHeat037Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat037Pass12]
  have h16 : nativeHeatPasses nativeGap038Old nativeHeat037Frames nativeHeat037Coef nativeHeat037Fixed nativeHeat037Base 16 nativeHeat037Y00 = nativeHeat037Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat037Pass16]
  have h20 : nativeHeatPasses nativeGap038Old nativeHeat037Frames nativeHeat037Coef nativeHeat037Fixed nativeHeat037Base 20 nativeHeat037Y00 = nativeHeat037Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat037Pass20]
  have h24 : nativeHeatPasses nativeGap038Old nativeHeat037Frames nativeHeat037Coef nativeHeat037Fixed nativeHeat037Base 24 nativeHeat037Y00 = nativeHeat037Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat037Pass24]
  have h28 : nativeHeatPasses nativeGap038Old nativeHeat037Frames nativeHeat037Coef nativeHeat037Fixed nativeHeat037Base 28 nativeHeat037Y00 = nativeHeat037Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat037Pass28]
  have h32 : nativeHeatPasses nativeGap038Old nativeHeat037Frames nativeHeat037Coef nativeHeat037Fixed nativeHeat037Base 32 nativeHeat037Y00 = nativeHeat037Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat037Pass32]
  have h36 : nativeHeatPasses nativeGap038Old nativeHeat037Frames nativeHeat037Coef nativeHeat037Fixed nativeHeat037Base 36 nativeHeat037Y00 = nativeHeat037Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat037Pass36]
  have h40 : nativeHeatPasses nativeGap038Old nativeHeat037Frames nativeHeat037Coef nativeHeat037Fixed nativeHeat037Base 40 nativeHeat037Y00 = nativeHeat037Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat037Pass40]
  have h44 : nativeHeatPasses nativeGap038Old nativeHeat037Frames nativeHeat037Coef nativeHeat037Fixed nativeHeat037Base 44 nativeHeat037Y00 = nativeHeat037Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat037Pass44]
  have h48 : nativeHeatPasses nativeGap038Old nativeHeat037Frames nativeHeat037Coef nativeHeat037Fixed nativeHeat037Base 48 nativeHeat037Y00 = nativeHeat037Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat037Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
