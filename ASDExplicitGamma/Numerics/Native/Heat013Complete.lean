module
public import ASDExplicitGamma.Numerics.Native.Heat013Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat013Y00_formula : nativeHeat013Y00 = nativeHeat013Frames.y := by
  decide +kernel

theorem nativeHeat013All48 : nativeHeatPasses nativeGap014Old nativeHeat013Frames nativeHeat013Coef nativeHeat013Fixed nativeHeat013Base 48 nativeHeat013Frames.y = nativeHeat013Y48 := by
  rw [← nativeHeat013Y00_formula]
  have h4 : nativeHeatPasses nativeGap014Old nativeHeat013Frames nativeHeat013Coef nativeHeat013Fixed nativeHeat013Base 4 nativeHeat013Y00 = nativeHeat013Y04 := nativeHeat013Pass04
  have h8 : nativeHeatPasses nativeGap014Old nativeHeat013Frames nativeHeat013Coef nativeHeat013Fixed nativeHeat013Base 8 nativeHeat013Y00 = nativeHeat013Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat013Pass08]
  have h12 : nativeHeatPasses nativeGap014Old nativeHeat013Frames nativeHeat013Coef nativeHeat013Fixed nativeHeat013Base 12 nativeHeat013Y00 = nativeHeat013Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat013Pass12]
  have h16 : nativeHeatPasses nativeGap014Old nativeHeat013Frames nativeHeat013Coef nativeHeat013Fixed nativeHeat013Base 16 nativeHeat013Y00 = nativeHeat013Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat013Pass16]
  have h20 : nativeHeatPasses nativeGap014Old nativeHeat013Frames nativeHeat013Coef nativeHeat013Fixed nativeHeat013Base 20 nativeHeat013Y00 = nativeHeat013Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat013Pass20]
  have h24 : nativeHeatPasses nativeGap014Old nativeHeat013Frames nativeHeat013Coef nativeHeat013Fixed nativeHeat013Base 24 nativeHeat013Y00 = nativeHeat013Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat013Pass24]
  have h28 : nativeHeatPasses nativeGap014Old nativeHeat013Frames nativeHeat013Coef nativeHeat013Fixed nativeHeat013Base 28 nativeHeat013Y00 = nativeHeat013Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat013Pass28]
  have h32 : nativeHeatPasses nativeGap014Old nativeHeat013Frames nativeHeat013Coef nativeHeat013Fixed nativeHeat013Base 32 nativeHeat013Y00 = nativeHeat013Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat013Pass32]
  have h36 : nativeHeatPasses nativeGap014Old nativeHeat013Frames nativeHeat013Coef nativeHeat013Fixed nativeHeat013Base 36 nativeHeat013Y00 = nativeHeat013Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat013Pass36]
  have h40 : nativeHeatPasses nativeGap014Old nativeHeat013Frames nativeHeat013Coef nativeHeat013Fixed nativeHeat013Base 40 nativeHeat013Y00 = nativeHeat013Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat013Pass40]
  have h44 : nativeHeatPasses nativeGap014Old nativeHeat013Frames nativeHeat013Coef nativeHeat013Fixed nativeHeat013Base 44 nativeHeat013Y00 = nativeHeat013Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat013Pass44]
  have h48 : nativeHeatPasses nativeGap014Old nativeHeat013Frames nativeHeat013Coef nativeHeat013Fixed nativeHeat013Base 48 nativeHeat013Y00 = nativeHeat013Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat013Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
