module
public import ASDExplicitGamma.Numerics.Native.Heat111Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat111Y00_formula : nativeHeat111Y00 = nativeHeat111Frames.y := by
  decide +kernel

theorem nativeHeat111All48 : nativeHeatPasses nativeGap112Old nativeHeat111Frames nativeHeat111Coef nativeHeat111Fixed nativeHeat111Base 48 nativeHeat111Frames.y = nativeHeat111Y48 := by
  rw [← nativeHeat111Y00_formula]
  have h4 : nativeHeatPasses nativeGap112Old nativeHeat111Frames nativeHeat111Coef nativeHeat111Fixed nativeHeat111Base 4 nativeHeat111Y00 = nativeHeat111Y04 := nativeHeat111Pass04
  have h8 : nativeHeatPasses nativeGap112Old nativeHeat111Frames nativeHeat111Coef nativeHeat111Fixed nativeHeat111Base 8 nativeHeat111Y00 = nativeHeat111Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat111Pass08]
  have h12 : nativeHeatPasses nativeGap112Old nativeHeat111Frames nativeHeat111Coef nativeHeat111Fixed nativeHeat111Base 12 nativeHeat111Y00 = nativeHeat111Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat111Pass12]
  have h16 : nativeHeatPasses nativeGap112Old nativeHeat111Frames nativeHeat111Coef nativeHeat111Fixed nativeHeat111Base 16 nativeHeat111Y00 = nativeHeat111Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat111Pass16]
  have h20 : nativeHeatPasses nativeGap112Old nativeHeat111Frames nativeHeat111Coef nativeHeat111Fixed nativeHeat111Base 20 nativeHeat111Y00 = nativeHeat111Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat111Pass20]
  have h24 : nativeHeatPasses nativeGap112Old nativeHeat111Frames nativeHeat111Coef nativeHeat111Fixed nativeHeat111Base 24 nativeHeat111Y00 = nativeHeat111Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat111Pass24]
  have h28 : nativeHeatPasses nativeGap112Old nativeHeat111Frames nativeHeat111Coef nativeHeat111Fixed nativeHeat111Base 28 nativeHeat111Y00 = nativeHeat111Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat111Pass28]
  have h32 : nativeHeatPasses nativeGap112Old nativeHeat111Frames nativeHeat111Coef nativeHeat111Fixed nativeHeat111Base 32 nativeHeat111Y00 = nativeHeat111Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat111Pass32]
  have h36 : nativeHeatPasses nativeGap112Old nativeHeat111Frames nativeHeat111Coef nativeHeat111Fixed nativeHeat111Base 36 nativeHeat111Y00 = nativeHeat111Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat111Pass36]
  have h40 : nativeHeatPasses nativeGap112Old nativeHeat111Frames nativeHeat111Coef nativeHeat111Fixed nativeHeat111Base 40 nativeHeat111Y00 = nativeHeat111Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat111Pass40]
  have h44 : nativeHeatPasses nativeGap112Old nativeHeat111Frames nativeHeat111Coef nativeHeat111Fixed nativeHeat111Base 44 nativeHeat111Y00 = nativeHeat111Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat111Pass44]
  have h48 : nativeHeatPasses nativeGap112Old nativeHeat111Frames nativeHeat111Coef nativeHeat111Fixed nativeHeat111Base 48 nativeHeat111Y00 = nativeHeat111Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat111Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
