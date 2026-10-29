module
public import ASDExplicitGamma.Numerics.Native.Heat155Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat155Y00_formula : nativeHeat155Y00 = nativeHeat155Frames.y := by
  decide +kernel

theorem nativeHeat155All48 : nativeHeatPasses nativeGap156Old nativeHeat155Frames nativeHeat155Coef nativeHeat155Fixed nativeHeat155Base 48 nativeHeat155Frames.y = nativeHeat155Y48 := by
  rw [← nativeHeat155Y00_formula]
  have h4 : nativeHeatPasses nativeGap156Old nativeHeat155Frames nativeHeat155Coef nativeHeat155Fixed nativeHeat155Base 4 nativeHeat155Y00 = nativeHeat155Y04 := nativeHeat155Pass04
  have h8 : nativeHeatPasses nativeGap156Old nativeHeat155Frames nativeHeat155Coef nativeHeat155Fixed nativeHeat155Base 8 nativeHeat155Y00 = nativeHeat155Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat155Pass08]
  have h12 : nativeHeatPasses nativeGap156Old nativeHeat155Frames nativeHeat155Coef nativeHeat155Fixed nativeHeat155Base 12 nativeHeat155Y00 = nativeHeat155Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat155Pass12]
  have h16 : nativeHeatPasses nativeGap156Old nativeHeat155Frames nativeHeat155Coef nativeHeat155Fixed nativeHeat155Base 16 nativeHeat155Y00 = nativeHeat155Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat155Pass16]
  have h20 : nativeHeatPasses nativeGap156Old nativeHeat155Frames nativeHeat155Coef nativeHeat155Fixed nativeHeat155Base 20 nativeHeat155Y00 = nativeHeat155Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat155Pass20]
  have h24 : nativeHeatPasses nativeGap156Old nativeHeat155Frames nativeHeat155Coef nativeHeat155Fixed nativeHeat155Base 24 nativeHeat155Y00 = nativeHeat155Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat155Pass24]
  have h28 : nativeHeatPasses nativeGap156Old nativeHeat155Frames nativeHeat155Coef nativeHeat155Fixed nativeHeat155Base 28 nativeHeat155Y00 = nativeHeat155Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat155Pass28]
  have h32 : nativeHeatPasses nativeGap156Old nativeHeat155Frames nativeHeat155Coef nativeHeat155Fixed nativeHeat155Base 32 nativeHeat155Y00 = nativeHeat155Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat155Pass32]
  have h36 : nativeHeatPasses nativeGap156Old nativeHeat155Frames nativeHeat155Coef nativeHeat155Fixed nativeHeat155Base 36 nativeHeat155Y00 = nativeHeat155Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat155Pass36]
  have h40 : nativeHeatPasses nativeGap156Old nativeHeat155Frames nativeHeat155Coef nativeHeat155Fixed nativeHeat155Base 40 nativeHeat155Y00 = nativeHeat155Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat155Pass40]
  have h44 : nativeHeatPasses nativeGap156Old nativeHeat155Frames nativeHeat155Coef nativeHeat155Fixed nativeHeat155Base 44 nativeHeat155Y00 = nativeHeat155Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat155Pass44]
  have h48 : nativeHeatPasses nativeGap156Old nativeHeat155Frames nativeHeat155Coef nativeHeat155Fixed nativeHeat155Base 48 nativeHeat155Y00 = nativeHeat155Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat155Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
