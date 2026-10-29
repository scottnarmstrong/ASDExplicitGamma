module
public import ASDExplicitGamma.Numerics.Native.Heat083Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat083Y00_formula : nativeHeat083Y00 = nativeHeat083Frames.y := by
  decide +kernel

theorem nativeHeat083All48 : nativeHeatPasses nativeGap084Old nativeHeat083Frames nativeHeat083Coef nativeHeat083Fixed nativeHeat083Base 48 nativeHeat083Frames.y = nativeHeat083Y48 := by
  rw [← nativeHeat083Y00_formula]
  have h4 : nativeHeatPasses nativeGap084Old nativeHeat083Frames nativeHeat083Coef nativeHeat083Fixed nativeHeat083Base 4 nativeHeat083Y00 = nativeHeat083Y04 := nativeHeat083Pass04
  have h8 : nativeHeatPasses nativeGap084Old nativeHeat083Frames nativeHeat083Coef nativeHeat083Fixed nativeHeat083Base 8 nativeHeat083Y00 = nativeHeat083Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat083Pass08]
  have h12 : nativeHeatPasses nativeGap084Old nativeHeat083Frames nativeHeat083Coef nativeHeat083Fixed nativeHeat083Base 12 nativeHeat083Y00 = nativeHeat083Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat083Pass12]
  have h16 : nativeHeatPasses nativeGap084Old nativeHeat083Frames nativeHeat083Coef nativeHeat083Fixed nativeHeat083Base 16 nativeHeat083Y00 = nativeHeat083Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat083Pass16]
  have h20 : nativeHeatPasses nativeGap084Old nativeHeat083Frames nativeHeat083Coef nativeHeat083Fixed nativeHeat083Base 20 nativeHeat083Y00 = nativeHeat083Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat083Pass20]
  have h24 : nativeHeatPasses nativeGap084Old nativeHeat083Frames nativeHeat083Coef nativeHeat083Fixed nativeHeat083Base 24 nativeHeat083Y00 = nativeHeat083Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat083Pass24]
  have h28 : nativeHeatPasses nativeGap084Old nativeHeat083Frames nativeHeat083Coef nativeHeat083Fixed nativeHeat083Base 28 nativeHeat083Y00 = nativeHeat083Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat083Pass28]
  have h32 : nativeHeatPasses nativeGap084Old nativeHeat083Frames nativeHeat083Coef nativeHeat083Fixed nativeHeat083Base 32 nativeHeat083Y00 = nativeHeat083Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat083Pass32]
  have h36 : nativeHeatPasses nativeGap084Old nativeHeat083Frames nativeHeat083Coef nativeHeat083Fixed nativeHeat083Base 36 nativeHeat083Y00 = nativeHeat083Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat083Pass36]
  have h40 : nativeHeatPasses nativeGap084Old nativeHeat083Frames nativeHeat083Coef nativeHeat083Fixed nativeHeat083Base 40 nativeHeat083Y00 = nativeHeat083Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat083Pass40]
  have h44 : nativeHeatPasses nativeGap084Old nativeHeat083Frames nativeHeat083Coef nativeHeat083Fixed nativeHeat083Base 44 nativeHeat083Y00 = nativeHeat083Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat083Pass44]
  have h48 : nativeHeatPasses nativeGap084Old nativeHeat083Frames nativeHeat083Coef nativeHeat083Fixed nativeHeat083Base 48 nativeHeat083Y00 = nativeHeat083Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat083Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
