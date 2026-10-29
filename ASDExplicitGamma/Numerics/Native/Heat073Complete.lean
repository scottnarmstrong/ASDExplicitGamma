module
public import ASDExplicitGamma.Numerics.Native.Heat073Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat073Y00_formula : nativeHeat073Y00 = nativeHeat073Frames.y := by
  decide +kernel

theorem nativeHeat073All48 : nativeHeatPasses nativeGap074Old nativeHeat073Frames nativeHeat073Coef nativeHeat073Fixed nativeHeat073Base 48 nativeHeat073Frames.y = nativeHeat073Y48 := by
  rw [← nativeHeat073Y00_formula]
  have h4 : nativeHeatPasses nativeGap074Old nativeHeat073Frames nativeHeat073Coef nativeHeat073Fixed nativeHeat073Base 4 nativeHeat073Y00 = nativeHeat073Y04 := nativeHeat073Pass04
  have h8 : nativeHeatPasses nativeGap074Old nativeHeat073Frames nativeHeat073Coef nativeHeat073Fixed nativeHeat073Base 8 nativeHeat073Y00 = nativeHeat073Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat073Pass08]
  have h12 : nativeHeatPasses nativeGap074Old nativeHeat073Frames nativeHeat073Coef nativeHeat073Fixed nativeHeat073Base 12 nativeHeat073Y00 = nativeHeat073Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat073Pass12]
  have h16 : nativeHeatPasses nativeGap074Old nativeHeat073Frames nativeHeat073Coef nativeHeat073Fixed nativeHeat073Base 16 nativeHeat073Y00 = nativeHeat073Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat073Pass16]
  have h20 : nativeHeatPasses nativeGap074Old nativeHeat073Frames nativeHeat073Coef nativeHeat073Fixed nativeHeat073Base 20 nativeHeat073Y00 = nativeHeat073Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat073Pass20]
  have h24 : nativeHeatPasses nativeGap074Old nativeHeat073Frames nativeHeat073Coef nativeHeat073Fixed nativeHeat073Base 24 nativeHeat073Y00 = nativeHeat073Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat073Pass24]
  have h28 : nativeHeatPasses nativeGap074Old nativeHeat073Frames nativeHeat073Coef nativeHeat073Fixed nativeHeat073Base 28 nativeHeat073Y00 = nativeHeat073Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat073Pass28]
  have h32 : nativeHeatPasses nativeGap074Old nativeHeat073Frames nativeHeat073Coef nativeHeat073Fixed nativeHeat073Base 32 nativeHeat073Y00 = nativeHeat073Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat073Pass32]
  have h36 : nativeHeatPasses nativeGap074Old nativeHeat073Frames nativeHeat073Coef nativeHeat073Fixed nativeHeat073Base 36 nativeHeat073Y00 = nativeHeat073Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat073Pass36]
  have h40 : nativeHeatPasses nativeGap074Old nativeHeat073Frames nativeHeat073Coef nativeHeat073Fixed nativeHeat073Base 40 nativeHeat073Y00 = nativeHeat073Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat073Pass40]
  have h44 : nativeHeatPasses nativeGap074Old nativeHeat073Frames nativeHeat073Coef nativeHeat073Fixed nativeHeat073Base 44 nativeHeat073Y00 = nativeHeat073Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat073Pass44]
  have h48 : nativeHeatPasses nativeGap074Old nativeHeat073Frames nativeHeat073Coef nativeHeat073Fixed nativeHeat073Base 48 nativeHeat073Y00 = nativeHeat073Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat073Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
