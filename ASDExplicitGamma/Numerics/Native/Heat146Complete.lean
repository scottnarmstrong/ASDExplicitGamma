module
public import ASDExplicitGamma.Numerics.Native.Heat146Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat146Y00_formula : nativeHeat146Y00 = nativeHeat146Frames.y := by
  decide +kernel

theorem nativeHeat146All48 : nativeHeatPasses nativeGap147Old nativeHeat146Frames nativeHeat146Coef nativeHeat146Fixed nativeHeat146Base 48 nativeHeat146Frames.y = nativeHeat146Y48 := by
  rw [← nativeHeat146Y00_formula]
  have h4 : nativeHeatPasses nativeGap147Old nativeHeat146Frames nativeHeat146Coef nativeHeat146Fixed nativeHeat146Base 4 nativeHeat146Y00 = nativeHeat146Y04 := nativeHeat146Pass04
  have h8 : nativeHeatPasses nativeGap147Old nativeHeat146Frames nativeHeat146Coef nativeHeat146Fixed nativeHeat146Base 8 nativeHeat146Y00 = nativeHeat146Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat146Pass08]
  have h12 : nativeHeatPasses nativeGap147Old nativeHeat146Frames nativeHeat146Coef nativeHeat146Fixed nativeHeat146Base 12 nativeHeat146Y00 = nativeHeat146Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat146Pass12]
  have h16 : nativeHeatPasses nativeGap147Old nativeHeat146Frames nativeHeat146Coef nativeHeat146Fixed nativeHeat146Base 16 nativeHeat146Y00 = nativeHeat146Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat146Pass16]
  have h20 : nativeHeatPasses nativeGap147Old nativeHeat146Frames nativeHeat146Coef nativeHeat146Fixed nativeHeat146Base 20 nativeHeat146Y00 = nativeHeat146Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat146Pass20]
  have h24 : nativeHeatPasses nativeGap147Old nativeHeat146Frames nativeHeat146Coef nativeHeat146Fixed nativeHeat146Base 24 nativeHeat146Y00 = nativeHeat146Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat146Pass24]
  have h28 : nativeHeatPasses nativeGap147Old nativeHeat146Frames nativeHeat146Coef nativeHeat146Fixed nativeHeat146Base 28 nativeHeat146Y00 = nativeHeat146Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat146Pass28]
  have h32 : nativeHeatPasses nativeGap147Old nativeHeat146Frames nativeHeat146Coef nativeHeat146Fixed nativeHeat146Base 32 nativeHeat146Y00 = nativeHeat146Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat146Pass32]
  have h36 : nativeHeatPasses nativeGap147Old nativeHeat146Frames nativeHeat146Coef nativeHeat146Fixed nativeHeat146Base 36 nativeHeat146Y00 = nativeHeat146Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat146Pass36]
  have h40 : nativeHeatPasses nativeGap147Old nativeHeat146Frames nativeHeat146Coef nativeHeat146Fixed nativeHeat146Base 40 nativeHeat146Y00 = nativeHeat146Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat146Pass40]
  have h44 : nativeHeatPasses nativeGap147Old nativeHeat146Frames nativeHeat146Coef nativeHeat146Fixed nativeHeat146Base 44 nativeHeat146Y00 = nativeHeat146Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat146Pass44]
  have h48 : nativeHeatPasses nativeGap147Old nativeHeat146Frames nativeHeat146Coef nativeHeat146Fixed nativeHeat146Base 48 nativeHeat146Y00 = nativeHeat146Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat146Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
