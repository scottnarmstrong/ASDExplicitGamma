module
public import ASDExplicitGamma.Numerics.Native.Heat042Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat042Y00_formula : nativeHeat042Y00 = nativeHeat042Frames.y := by
  decide +kernel

theorem nativeHeat042All48 : nativeHeatPasses nativeGap043Old nativeHeat042Frames nativeHeat042Coef nativeHeat042Fixed nativeHeat042Base 48 nativeHeat042Frames.y = nativeHeat042Y48 := by
  rw [← nativeHeat042Y00_formula]
  have h4 : nativeHeatPasses nativeGap043Old nativeHeat042Frames nativeHeat042Coef nativeHeat042Fixed nativeHeat042Base 4 nativeHeat042Y00 = nativeHeat042Y04 := nativeHeat042Pass04
  have h8 : nativeHeatPasses nativeGap043Old nativeHeat042Frames nativeHeat042Coef nativeHeat042Fixed nativeHeat042Base 8 nativeHeat042Y00 = nativeHeat042Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat042Pass08]
  have h12 : nativeHeatPasses nativeGap043Old nativeHeat042Frames nativeHeat042Coef nativeHeat042Fixed nativeHeat042Base 12 nativeHeat042Y00 = nativeHeat042Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat042Pass12]
  have h16 : nativeHeatPasses nativeGap043Old nativeHeat042Frames nativeHeat042Coef nativeHeat042Fixed nativeHeat042Base 16 nativeHeat042Y00 = nativeHeat042Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat042Pass16]
  have h20 : nativeHeatPasses nativeGap043Old nativeHeat042Frames nativeHeat042Coef nativeHeat042Fixed nativeHeat042Base 20 nativeHeat042Y00 = nativeHeat042Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat042Pass20]
  have h24 : nativeHeatPasses nativeGap043Old nativeHeat042Frames nativeHeat042Coef nativeHeat042Fixed nativeHeat042Base 24 nativeHeat042Y00 = nativeHeat042Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat042Pass24]
  have h28 : nativeHeatPasses nativeGap043Old nativeHeat042Frames nativeHeat042Coef nativeHeat042Fixed nativeHeat042Base 28 nativeHeat042Y00 = nativeHeat042Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat042Pass28]
  have h32 : nativeHeatPasses nativeGap043Old nativeHeat042Frames nativeHeat042Coef nativeHeat042Fixed nativeHeat042Base 32 nativeHeat042Y00 = nativeHeat042Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat042Pass32]
  have h36 : nativeHeatPasses nativeGap043Old nativeHeat042Frames nativeHeat042Coef nativeHeat042Fixed nativeHeat042Base 36 nativeHeat042Y00 = nativeHeat042Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat042Pass36]
  have h40 : nativeHeatPasses nativeGap043Old nativeHeat042Frames nativeHeat042Coef nativeHeat042Fixed nativeHeat042Base 40 nativeHeat042Y00 = nativeHeat042Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat042Pass40]
  have h44 : nativeHeatPasses nativeGap043Old nativeHeat042Frames nativeHeat042Coef nativeHeat042Fixed nativeHeat042Base 44 nativeHeat042Y00 = nativeHeat042Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat042Pass44]
  have h48 : nativeHeatPasses nativeGap043Old nativeHeat042Frames nativeHeat042Coef nativeHeat042Fixed nativeHeat042Base 48 nativeHeat042Y00 = nativeHeat042Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat042Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
