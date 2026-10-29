module
public import ASDExplicitGamma.Numerics.Native.Heat099Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat099Y00_formula : nativeHeat099Y00 = nativeHeat099Frames.y := by
  decide +kernel

theorem nativeHeat099All48 : nativeHeatPasses nativeGap100Old nativeHeat099Frames nativeHeat099Coef nativeHeat099Fixed nativeHeat099Base 48 nativeHeat099Frames.y = nativeHeat099Y48 := by
  rw [← nativeHeat099Y00_formula]
  have h4 : nativeHeatPasses nativeGap100Old nativeHeat099Frames nativeHeat099Coef nativeHeat099Fixed nativeHeat099Base 4 nativeHeat099Y00 = nativeHeat099Y04 := nativeHeat099Pass04
  have h8 : nativeHeatPasses nativeGap100Old nativeHeat099Frames nativeHeat099Coef nativeHeat099Fixed nativeHeat099Base 8 nativeHeat099Y00 = nativeHeat099Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat099Pass08]
  have h12 : nativeHeatPasses nativeGap100Old nativeHeat099Frames nativeHeat099Coef nativeHeat099Fixed nativeHeat099Base 12 nativeHeat099Y00 = nativeHeat099Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat099Pass12]
  have h16 : nativeHeatPasses nativeGap100Old nativeHeat099Frames nativeHeat099Coef nativeHeat099Fixed nativeHeat099Base 16 nativeHeat099Y00 = nativeHeat099Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat099Pass16]
  have h20 : nativeHeatPasses nativeGap100Old nativeHeat099Frames nativeHeat099Coef nativeHeat099Fixed nativeHeat099Base 20 nativeHeat099Y00 = nativeHeat099Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat099Pass20]
  have h24 : nativeHeatPasses nativeGap100Old nativeHeat099Frames nativeHeat099Coef nativeHeat099Fixed nativeHeat099Base 24 nativeHeat099Y00 = nativeHeat099Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat099Pass24]
  have h28 : nativeHeatPasses nativeGap100Old nativeHeat099Frames nativeHeat099Coef nativeHeat099Fixed nativeHeat099Base 28 nativeHeat099Y00 = nativeHeat099Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat099Pass28]
  have h32 : nativeHeatPasses nativeGap100Old nativeHeat099Frames nativeHeat099Coef nativeHeat099Fixed nativeHeat099Base 32 nativeHeat099Y00 = nativeHeat099Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat099Pass32]
  have h36 : nativeHeatPasses nativeGap100Old nativeHeat099Frames nativeHeat099Coef nativeHeat099Fixed nativeHeat099Base 36 nativeHeat099Y00 = nativeHeat099Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat099Pass36]
  have h40 : nativeHeatPasses nativeGap100Old nativeHeat099Frames nativeHeat099Coef nativeHeat099Fixed nativeHeat099Base 40 nativeHeat099Y00 = nativeHeat099Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat099Pass40]
  have h44 : nativeHeatPasses nativeGap100Old nativeHeat099Frames nativeHeat099Coef nativeHeat099Fixed nativeHeat099Base 44 nativeHeat099Y00 = nativeHeat099Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat099Pass44]
  have h48 : nativeHeatPasses nativeGap100Old nativeHeat099Frames nativeHeat099Coef nativeHeat099Fixed nativeHeat099Base 48 nativeHeat099Y00 = nativeHeat099Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat099Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
