module
public import ASDExplicitGamma.Numerics.Native.Heat051Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat051Y00_formula : nativeHeat051Y00 = nativeHeat051Frames.y := by
  decide +kernel

theorem nativeHeat051All48 : nativeHeatPasses nativeGap052Old nativeHeat051Frames nativeHeat051Coef nativeHeat051Fixed nativeHeat051Base 48 nativeHeat051Frames.y = nativeHeat051Y48 := by
  rw [← nativeHeat051Y00_formula]
  have h4 : nativeHeatPasses nativeGap052Old nativeHeat051Frames nativeHeat051Coef nativeHeat051Fixed nativeHeat051Base 4 nativeHeat051Y00 = nativeHeat051Y04 := nativeHeat051Pass04
  have h8 : nativeHeatPasses nativeGap052Old nativeHeat051Frames nativeHeat051Coef nativeHeat051Fixed nativeHeat051Base 8 nativeHeat051Y00 = nativeHeat051Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat051Pass08]
  have h12 : nativeHeatPasses nativeGap052Old nativeHeat051Frames nativeHeat051Coef nativeHeat051Fixed nativeHeat051Base 12 nativeHeat051Y00 = nativeHeat051Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat051Pass12]
  have h16 : nativeHeatPasses nativeGap052Old nativeHeat051Frames nativeHeat051Coef nativeHeat051Fixed nativeHeat051Base 16 nativeHeat051Y00 = nativeHeat051Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat051Pass16]
  have h20 : nativeHeatPasses nativeGap052Old nativeHeat051Frames nativeHeat051Coef nativeHeat051Fixed nativeHeat051Base 20 nativeHeat051Y00 = nativeHeat051Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat051Pass20]
  have h24 : nativeHeatPasses nativeGap052Old nativeHeat051Frames nativeHeat051Coef nativeHeat051Fixed nativeHeat051Base 24 nativeHeat051Y00 = nativeHeat051Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat051Pass24]
  have h28 : nativeHeatPasses nativeGap052Old nativeHeat051Frames nativeHeat051Coef nativeHeat051Fixed nativeHeat051Base 28 nativeHeat051Y00 = nativeHeat051Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat051Pass28]
  have h32 : nativeHeatPasses nativeGap052Old nativeHeat051Frames nativeHeat051Coef nativeHeat051Fixed nativeHeat051Base 32 nativeHeat051Y00 = nativeHeat051Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat051Pass32]
  have h36 : nativeHeatPasses nativeGap052Old nativeHeat051Frames nativeHeat051Coef nativeHeat051Fixed nativeHeat051Base 36 nativeHeat051Y00 = nativeHeat051Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat051Pass36]
  have h40 : nativeHeatPasses nativeGap052Old nativeHeat051Frames nativeHeat051Coef nativeHeat051Fixed nativeHeat051Base 40 nativeHeat051Y00 = nativeHeat051Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat051Pass40]
  have h44 : nativeHeatPasses nativeGap052Old nativeHeat051Frames nativeHeat051Coef nativeHeat051Fixed nativeHeat051Base 44 nativeHeat051Y00 = nativeHeat051Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat051Pass44]
  have h48 : nativeHeatPasses nativeGap052Old nativeHeat051Frames nativeHeat051Coef nativeHeat051Fixed nativeHeat051Base 48 nativeHeat051Y00 = nativeHeat051Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat051Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
