module
public import ASDExplicitGamma.Numerics.Native.Heat154Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat154Y00_formula : nativeHeat154Y00 = nativeHeat154Frames.y := by
  decide +kernel

theorem nativeHeat154All48 : nativeHeatPasses nativeGap155Old nativeHeat154Frames nativeHeat154Coef nativeHeat154Fixed nativeHeat154Base 48 nativeHeat154Frames.y = nativeHeat154Y48 := by
  rw [← nativeHeat154Y00_formula]
  have h4 : nativeHeatPasses nativeGap155Old nativeHeat154Frames nativeHeat154Coef nativeHeat154Fixed nativeHeat154Base 4 nativeHeat154Y00 = nativeHeat154Y04 := nativeHeat154Pass04
  have h8 : nativeHeatPasses nativeGap155Old nativeHeat154Frames nativeHeat154Coef nativeHeat154Fixed nativeHeat154Base 8 nativeHeat154Y00 = nativeHeat154Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat154Pass08]
  have h12 : nativeHeatPasses nativeGap155Old nativeHeat154Frames nativeHeat154Coef nativeHeat154Fixed nativeHeat154Base 12 nativeHeat154Y00 = nativeHeat154Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat154Pass12]
  have h16 : nativeHeatPasses nativeGap155Old nativeHeat154Frames nativeHeat154Coef nativeHeat154Fixed nativeHeat154Base 16 nativeHeat154Y00 = nativeHeat154Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat154Pass16]
  have h20 : nativeHeatPasses nativeGap155Old nativeHeat154Frames nativeHeat154Coef nativeHeat154Fixed nativeHeat154Base 20 nativeHeat154Y00 = nativeHeat154Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat154Pass20]
  have h24 : nativeHeatPasses nativeGap155Old nativeHeat154Frames nativeHeat154Coef nativeHeat154Fixed nativeHeat154Base 24 nativeHeat154Y00 = nativeHeat154Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat154Pass24]
  have h28 : nativeHeatPasses nativeGap155Old nativeHeat154Frames nativeHeat154Coef nativeHeat154Fixed nativeHeat154Base 28 nativeHeat154Y00 = nativeHeat154Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat154Pass28]
  have h32 : nativeHeatPasses nativeGap155Old nativeHeat154Frames nativeHeat154Coef nativeHeat154Fixed nativeHeat154Base 32 nativeHeat154Y00 = nativeHeat154Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat154Pass32]
  have h36 : nativeHeatPasses nativeGap155Old nativeHeat154Frames nativeHeat154Coef nativeHeat154Fixed nativeHeat154Base 36 nativeHeat154Y00 = nativeHeat154Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat154Pass36]
  have h40 : nativeHeatPasses nativeGap155Old nativeHeat154Frames nativeHeat154Coef nativeHeat154Fixed nativeHeat154Base 40 nativeHeat154Y00 = nativeHeat154Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat154Pass40]
  have h44 : nativeHeatPasses nativeGap155Old nativeHeat154Frames nativeHeat154Coef nativeHeat154Fixed nativeHeat154Base 44 nativeHeat154Y00 = nativeHeat154Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat154Pass44]
  have h48 : nativeHeatPasses nativeGap155Old nativeHeat154Frames nativeHeat154Coef nativeHeat154Fixed nativeHeat154Base 48 nativeHeat154Y00 = nativeHeat154Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat154Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
