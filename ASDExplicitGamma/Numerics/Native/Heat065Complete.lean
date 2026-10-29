module
public import ASDExplicitGamma.Numerics.Native.Heat065Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat065Y00_formula : nativeHeat065Y00 = nativeHeat065Frames.y := by
  decide +kernel

theorem nativeHeat065All48 : nativeHeatPasses nativeGap066Old nativeHeat065Frames nativeHeat065Coef nativeHeat065Fixed nativeHeat065Base 48 nativeHeat065Frames.y = nativeHeat065Y48 := by
  rw [← nativeHeat065Y00_formula]
  have h4 : nativeHeatPasses nativeGap066Old nativeHeat065Frames nativeHeat065Coef nativeHeat065Fixed nativeHeat065Base 4 nativeHeat065Y00 = nativeHeat065Y04 := nativeHeat065Pass04
  have h8 : nativeHeatPasses nativeGap066Old nativeHeat065Frames nativeHeat065Coef nativeHeat065Fixed nativeHeat065Base 8 nativeHeat065Y00 = nativeHeat065Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat065Pass08]
  have h12 : nativeHeatPasses nativeGap066Old nativeHeat065Frames nativeHeat065Coef nativeHeat065Fixed nativeHeat065Base 12 nativeHeat065Y00 = nativeHeat065Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat065Pass12]
  have h16 : nativeHeatPasses nativeGap066Old nativeHeat065Frames nativeHeat065Coef nativeHeat065Fixed nativeHeat065Base 16 nativeHeat065Y00 = nativeHeat065Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat065Pass16]
  have h20 : nativeHeatPasses nativeGap066Old nativeHeat065Frames nativeHeat065Coef nativeHeat065Fixed nativeHeat065Base 20 nativeHeat065Y00 = nativeHeat065Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat065Pass20]
  have h24 : nativeHeatPasses nativeGap066Old nativeHeat065Frames nativeHeat065Coef nativeHeat065Fixed nativeHeat065Base 24 nativeHeat065Y00 = nativeHeat065Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat065Pass24]
  have h28 : nativeHeatPasses nativeGap066Old nativeHeat065Frames nativeHeat065Coef nativeHeat065Fixed nativeHeat065Base 28 nativeHeat065Y00 = nativeHeat065Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat065Pass28]
  have h32 : nativeHeatPasses nativeGap066Old nativeHeat065Frames nativeHeat065Coef nativeHeat065Fixed nativeHeat065Base 32 nativeHeat065Y00 = nativeHeat065Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat065Pass32]
  have h36 : nativeHeatPasses nativeGap066Old nativeHeat065Frames nativeHeat065Coef nativeHeat065Fixed nativeHeat065Base 36 nativeHeat065Y00 = nativeHeat065Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat065Pass36]
  have h40 : nativeHeatPasses nativeGap066Old nativeHeat065Frames nativeHeat065Coef nativeHeat065Fixed nativeHeat065Base 40 nativeHeat065Y00 = nativeHeat065Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat065Pass40]
  have h44 : nativeHeatPasses nativeGap066Old nativeHeat065Frames nativeHeat065Coef nativeHeat065Fixed nativeHeat065Base 44 nativeHeat065Y00 = nativeHeat065Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat065Pass44]
  have h48 : nativeHeatPasses nativeGap066Old nativeHeat065Frames nativeHeat065Coef nativeHeat065Fixed nativeHeat065Base 48 nativeHeat065Y00 = nativeHeat065Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat065Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
