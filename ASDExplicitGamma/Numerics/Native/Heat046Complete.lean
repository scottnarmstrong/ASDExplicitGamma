module
public import ASDExplicitGamma.Numerics.Native.Heat046Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat046Y00_formula : nativeHeat046Y00 = nativeHeat046Frames.y := by
  decide +kernel

theorem nativeHeat046All48 : nativeHeatPasses nativeGap047Old nativeHeat046Frames nativeHeat046Coef nativeHeat046Fixed nativeHeat046Base 48 nativeHeat046Frames.y = nativeHeat046Y48 := by
  rw [← nativeHeat046Y00_formula]
  have h4 : nativeHeatPasses nativeGap047Old nativeHeat046Frames nativeHeat046Coef nativeHeat046Fixed nativeHeat046Base 4 nativeHeat046Y00 = nativeHeat046Y04 := nativeHeat046Pass04
  have h8 : nativeHeatPasses nativeGap047Old nativeHeat046Frames nativeHeat046Coef nativeHeat046Fixed nativeHeat046Base 8 nativeHeat046Y00 = nativeHeat046Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat046Pass08]
  have h12 : nativeHeatPasses nativeGap047Old nativeHeat046Frames nativeHeat046Coef nativeHeat046Fixed nativeHeat046Base 12 nativeHeat046Y00 = nativeHeat046Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat046Pass12]
  have h16 : nativeHeatPasses nativeGap047Old nativeHeat046Frames nativeHeat046Coef nativeHeat046Fixed nativeHeat046Base 16 nativeHeat046Y00 = nativeHeat046Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat046Pass16]
  have h20 : nativeHeatPasses nativeGap047Old nativeHeat046Frames nativeHeat046Coef nativeHeat046Fixed nativeHeat046Base 20 nativeHeat046Y00 = nativeHeat046Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat046Pass20]
  have h24 : nativeHeatPasses nativeGap047Old nativeHeat046Frames nativeHeat046Coef nativeHeat046Fixed nativeHeat046Base 24 nativeHeat046Y00 = nativeHeat046Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat046Pass24]
  have h28 : nativeHeatPasses nativeGap047Old nativeHeat046Frames nativeHeat046Coef nativeHeat046Fixed nativeHeat046Base 28 nativeHeat046Y00 = nativeHeat046Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat046Pass28]
  have h32 : nativeHeatPasses nativeGap047Old nativeHeat046Frames nativeHeat046Coef nativeHeat046Fixed nativeHeat046Base 32 nativeHeat046Y00 = nativeHeat046Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat046Pass32]
  have h36 : nativeHeatPasses nativeGap047Old nativeHeat046Frames nativeHeat046Coef nativeHeat046Fixed nativeHeat046Base 36 nativeHeat046Y00 = nativeHeat046Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat046Pass36]
  have h40 : nativeHeatPasses nativeGap047Old nativeHeat046Frames nativeHeat046Coef nativeHeat046Fixed nativeHeat046Base 40 nativeHeat046Y00 = nativeHeat046Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat046Pass40]
  have h44 : nativeHeatPasses nativeGap047Old nativeHeat046Frames nativeHeat046Coef nativeHeat046Fixed nativeHeat046Base 44 nativeHeat046Y00 = nativeHeat046Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat046Pass44]
  have h48 : nativeHeatPasses nativeGap047Old nativeHeat046Frames nativeHeat046Coef nativeHeat046Fixed nativeHeat046Base 48 nativeHeat046Y00 = nativeHeat046Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat046Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
