module
public import ASDExplicitGamma.Numerics.Native.Heat063Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat063Y00_formula : nativeHeat063Y00 = nativeHeat063Frames.y := by
  decide +kernel

theorem nativeHeat063All48 : nativeHeatPasses nativeGap064Old nativeHeat063Frames nativeHeat063Coef nativeHeat063Fixed nativeHeat063Base 48 nativeHeat063Frames.y = nativeHeat063Y48 := by
  rw [← nativeHeat063Y00_formula]
  have h4 : nativeHeatPasses nativeGap064Old nativeHeat063Frames nativeHeat063Coef nativeHeat063Fixed nativeHeat063Base 4 nativeHeat063Y00 = nativeHeat063Y04 := nativeHeat063Pass04
  have h8 : nativeHeatPasses nativeGap064Old nativeHeat063Frames nativeHeat063Coef nativeHeat063Fixed nativeHeat063Base 8 nativeHeat063Y00 = nativeHeat063Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat063Pass08]
  have h12 : nativeHeatPasses nativeGap064Old nativeHeat063Frames nativeHeat063Coef nativeHeat063Fixed nativeHeat063Base 12 nativeHeat063Y00 = nativeHeat063Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat063Pass12]
  have h16 : nativeHeatPasses nativeGap064Old nativeHeat063Frames nativeHeat063Coef nativeHeat063Fixed nativeHeat063Base 16 nativeHeat063Y00 = nativeHeat063Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat063Pass16]
  have h20 : nativeHeatPasses nativeGap064Old nativeHeat063Frames nativeHeat063Coef nativeHeat063Fixed nativeHeat063Base 20 nativeHeat063Y00 = nativeHeat063Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat063Pass20]
  have h24 : nativeHeatPasses nativeGap064Old nativeHeat063Frames nativeHeat063Coef nativeHeat063Fixed nativeHeat063Base 24 nativeHeat063Y00 = nativeHeat063Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat063Pass24]
  have h28 : nativeHeatPasses nativeGap064Old nativeHeat063Frames nativeHeat063Coef nativeHeat063Fixed nativeHeat063Base 28 nativeHeat063Y00 = nativeHeat063Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat063Pass28]
  have h32 : nativeHeatPasses nativeGap064Old nativeHeat063Frames nativeHeat063Coef nativeHeat063Fixed nativeHeat063Base 32 nativeHeat063Y00 = nativeHeat063Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat063Pass32]
  have h36 : nativeHeatPasses nativeGap064Old nativeHeat063Frames nativeHeat063Coef nativeHeat063Fixed nativeHeat063Base 36 nativeHeat063Y00 = nativeHeat063Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat063Pass36]
  have h40 : nativeHeatPasses nativeGap064Old nativeHeat063Frames nativeHeat063Coef nativeHeat063Fixed nativeHeat063Base 40 nativeHeat063Y00 = nativeHeat063Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat063Pass40]
  have h44 : nativeHeatPasses nativeGap064Old nativeHeat063Frames nativeHeat063Coef nativeHeat063Fixed nativeHeat063Base 44 nativeHeat063Y00 = nativeHeat063Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat063Pass44]
  have h48 : nativeHeatPasses nativeGap064Old nativeHeat063Frames nativeHeat063Coef nativeHeat063Fixed nativeHeat063Base 48 nativeHeat063Y00 = nativeHeat063Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat063Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
