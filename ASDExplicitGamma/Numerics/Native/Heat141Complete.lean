module
public import ASDExplicitGamma.Numerics.Native.Heat141Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat141Y00_formula : nativeHeat141Y00 = nativeHeat141Frames.y := by
  decide +kernel

theorem nativeHeat141All48 : nativeHeatPasses nativeGap142Old nativeHeat141Frames nativeHeat141Coef nativeHeat141Fixed nativeHeat141Base 48 nativeHeat141Frames.y = nativeHeat141Y48 := by
  rw [← nativeHeat141Y00_formula]
  have h4 : nativeHeatPasses nativeGap142Old nativeHeat141Frames nativeHeat141Coef nativeHeat141Fixed nativeHeat141Base 4 nativeHeat141Y00 = nativeHeat141Y04 := nativeHeat141Pass04
  have h8 : nativeHeatPasses nativeGap142Old nativeHeat141Frames nativeHeat141Coef nativeHeat141Fixed nativeHeat141Base 8 nativeHeat141Y00 = nativeHeat141Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat141Pass08]
  have h12 : nativeHeatPasses nativeGap142Old nativeHeat141Frames nativeHeat141Coef nativeHeat141Fixed nativeHeat141Base 12 nativeHeat141Y00 = nativeHeat141Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat141Pass12]
  have h16 : nativeHeatPasses nativeGap142Old nativeHeat141Frames nativeHeat141Coef nativeHeat141Fixed nativeHeat141Base 16 nativeHeat141Y00 = nativeHeat141Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat141Pass16]
  have h20 : nativeHeatPasses nativeGap142Old nativeHeat141Frames nativeHeat141Coef nativeHeat141Fixed nativeHeat141Base 20 nativeHeat141Y00 = nativeHeat141Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat141Pass20]
  have h24 : nativeHeatPasses nativeGap142Old nativeHeat141Frames nativeHeat141Coef nativeHeat141Fixed nativeHeat141Base 24 nativeHeat141Y00 = nativeHeat141Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat141Pass24]
  have h28 : nativeHeatPasses nativeGap142Old nativeHeat141Frames nativeHeat141Coef nativeHeat141Fixed nativeHeat141Base 28 nativeHeat141Y00 = nativeHeat141Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat141Pass28]
  have h32 : nativeHeatPasses nativeGap142Old nativeHeat141Frames nativeHeat141Coef nativeHeat141Fixed nativeHeat141Base 32 nativeHeat141Y00 = nativeHeat141Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat141Pass32]
  have h36 : nativeHeatPasses nativeGap142Old nativeHeat141Frames nativeHeat141Coef nativeHeat141Fixed nativeHeat141Base 36 nativeHeat141Y00 = nativeHeat141Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat141Pass36]
  have h40 : nativeHeatPasses nativeGap142Old nativeHeat141Frames nativeHeat141Coef nativeHeat141Fixed nativeHeat141Base 40 nativeHeat141Y00 = nativeHeat141Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat141Pass40]
  have h44 : nativeHeatPasses nativeGap142Old nativeHeat141Frames nativeHeat141Coef nativeHeat141Fixed nativeHeat141Base 44 nativeHeat141Y00 = nativeHeat141Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat141Pass44]
  have h48 : nativeHeatPasses nativeGap142Old nativeHeat141Frames nativeHeat141Coef nativeHeat141Fixed nativeHeat141Base 48 nativeHeat141Y00 = nativeHeat141Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat141Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
