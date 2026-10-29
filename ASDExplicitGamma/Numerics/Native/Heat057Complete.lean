module
public import ASDExplicitGamma.Numerics.Native.Heat057Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat057Y00_formula : nativeHeat057Y00 = nativeHeat057Frames.y := by
  decide +kernel

theorem nativeHeat057All48 : nativeHeatPasses nativeGap058Old nativeHeat057Frames nativeHeat057Coef nativeHeat057Fixed nativeHeat057Base 48 nativeHeat057Frames.y = nativeHeat057Y48 := by
  rw [← nativeHeat057Y00_formula]
  have h4 : nativeHeatPasses nativeGap058Old nativeHeat057Frames nativeHeat057Coef nativeHeat057Fixed nativeHeat057Base 4 nativeHeat057Y00 = nativeHeat057Y04 := nativeHeat057Pass04
  have h8 : nativeHeatPasses nativeGap058Old nativeHeat057Frames nativeHeat057Coef nativeHeat057Fixed nativeHeat057Base 8 nativeHeat057Y00 = nativeHeat057Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat057Pass08]
  have h12 : nativeHeatPasses nativeGap058Old nativeHeat057Frames nativeHeat057Coef nativeHeat057Fixed nativeHeat057Base 12 nativeHeat057Y00 = nativeHeat057Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat057Pass12]
  have h16 : nativeHeatPasses nativeGap058Old nativeHeat057Frames nativeHeat057Coef nativeHeat057Fixed nativeHeat057Base 16 nativeHeat057Y00 = nativeHeat057Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat057Pass16]
  have h20 : nativeHeatPasses nativeGap058Old nativeHeat057Frames nativeHeat057Coef nativeHeat057Fixed nativeHeat057Base 20 nativeHeat057Y00 = nativeHeat057Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat057Pass20]
  have h24 : nativeHeatPasses nativeGap058Old nativeHeat057Frames nativeHeat057Coef nativeHeat057Fixed nativeHeat057Base 24 nativeHeat057Y00 = nativeHeat057Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat057Pass24]
  have h28 : nativeHeatPasses nativeGap058Old nativeHeat057Frames nativeHeat057Coef nativeHeat057Fixed nativeHeat057Base 28 nativeHeat057Y00 = nativeHeat057Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat057Pass28]
  have h32 : nativeHeatPasses nativeGap058Old nativeHeat057Frames nativeHeat057Coef nativeHeat057Fixed nativeHeat057Base 32 nativeHeat057Y00 = nativeHeat057Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat057Pass32]
  have h36 : nativeHeatPasses nativeGap058Old nativeHeat057Frames nativeHeat057Coef nativeHeat057Fixed nativeHeat057Base 36 nativeHeat057Y00 = nativeHeat057Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat057Pass36]
  have h40 : nativeHeatPasses nativeGap058Old nativeHeat057Frames nativeHeat057Coef nativeHeat057Fixed nativeHeat057Base 40 nativeHeat057Y00 = nativeHeat057Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat057Pass40]
  have h44 : nativeHeatPasses nativeGap058Old nativeHeat057Frames nativeHeat057Coef nativeHeat057Fixed nativeHeat057Base 44 nativeHeat057Y00 = nativeHeat057Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat057Pass44]
  have h48 : nativeHeatPasses nativeGap058Old nativeHeat057Frames nativeHeat057Coef nativeHeat057Fixed nativeHeat057Base 48 nativeHeat057Y00 = nativeHeat057Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat057Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
