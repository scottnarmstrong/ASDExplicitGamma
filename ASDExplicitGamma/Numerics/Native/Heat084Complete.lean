module
public import ASDExplicitGamma.Numerics.Native.Heat084Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat084Y00_formula : nativeHeat084Y00 = nativeHeat084Frames.y := by
  decide +kernel

theorem nativeHeat084All48 : nativeHeatPasses nativeGap085Old nativeHeat084Frames nativeHeat084Coef nativeHeat084Fixed nativeHeat084Base 48 nativeHeat084Frames.y = nativeHeat084Y48 := by
  rw [← nativeHeat084Y00_formula]
  have h4 : nativeHeatPasses nativeGap085Old nativeHeat084Frames nativeHeat084Coef nativeHeat084Fixed nativeHeat084Base 4 nativeHeat084Y00 = nativeHeat084Y04 := nativeHeat084Pass04
  have h8 : nativeHeatPasses nativeGap085Old nativeHeat084Frames nativeHeat084Coef nativeHeat084Fixed nativeHeat084Base 8 nativeHeat084Y00 = nativeHeat084Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat084Pass08]
  have h12 : nativeHeatPasses nativeGap085Old nativeHeat084Frames nativeHeat084Coef nativeHeat084Fixed nativeHeat084Base 12 nativeHeat084Y00 = nativeHeat084Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat084Pass12]
  have h16 : nativeHeatPasses nativeGap085Old nativeHeat084Frames nativeHeat084Coef nativeHeat084Fixed nativeHeat084Base 16 nativeHeat084Y00 = nativeHeat084Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat084Pass16]
  have h20 : nativeHeatPasses nativeGap085Old nativeHeat084Frames nativeHeat084Coef nativeHeat084Fixed nativeHeat084Base 20 nativeHeat084Y00 = nativeHeat084Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat084Pass20]
  have h24 : nativeHeatPasses nativeGap085Old nativeHeat084Frames nativeHeat084Coef nativeHeat084Fixed nativeHeat084Base 24 nativeHeat084Y00 = nativeHeat084Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat084Pass24]
  have h28 : nativeHeatPasses nativeGap085Old nativeHeat084Frames nativeHeat084Coef nativeHeat084Fixed nativeHeat084Base 28 nativeHeat084Y00 = nativeHeat084Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat084Pass28]
  have h32 : nativeHeatPasses nativeGap085Old nativeHeat084Frames nativeHeat084Coef nativeHeat084Fixed nativeHeat084Base 32 nativeHeat084Y00 = nativeHeat084Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat084Pass32]
  have h36 : nativeHeatPasses nativeGap085Old nativeHeat084Frames nativeHeat084Coef nativeHeat084Fixed nativeHeat084Base 36 nativeHeat084Y00 = nativeHeat084Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat084Pass36]
  have h40 : nativeHeatPasses nativeGap085Old nativeHeat084Frames nativeHeat084Coef nativeHeat084Fixed nativeHeat084Base 40 nativeHeat084Y00 = nativeHeat084Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat084Pass40]
  have h44 : nativeHeatPasses nativeGap085Old nativeHeat084Frames nativeHeat084Coef nativeHeat084Fixed nativeHeat084Base 44 nativeHeat084Y00 = nativeHeat084Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat084Pass44]
  have h48 : nativeHeatPasses nativeGap085Old nativeHeat084Frames nativeHeat084Coef nativeHeat084Fixed nativeHeat084Base 48 nativeHeat084Y00 = nativeHeat084Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat084Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
