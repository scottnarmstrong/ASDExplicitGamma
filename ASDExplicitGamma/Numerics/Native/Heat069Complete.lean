module
public import ASDExplicitGamma.Numerics.Native.Heat069Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat069Y00_formula : nativeHeat069Y00 = nativeHeat069Frames.y := by
  decide +kernel

theorem nativeHeat069All48 : nativeHeatPasses nativeGap070Old nativeHeat069Frames nativeHeat069Coef nativeHeat069Fixed nativeHeat069Base 48 nativeHeat069Frames.y = nativeHeat069Y48 := by
  rw [← nativeHeat069Y00_formula]
  have h4 : nativeHeatPasses nativeGap070Old nativeHeat069Frames nativeHeat069Coef nativeHeat069Fixed nativeHeat069Base 4 nativeHeat069Y00 = nativeHeat069Y04 := nativeHeat069Pass04
  have h8 : nativeHeatPasses nativeGap070Old nativeHeat069Frames nativeHeat069Coef nativeHeat069Fixed nativeHeat069Base 8 nativeHeat069Y00 = nativeHeat069Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat069Pass08]
  have h12 : nativeHeatPasses nativeGap070Old nativeHeat069Frames nativeHeat069Coef nativeHeat069Fixed nativeHeat069Base 12 nativeHeat069Y00 = nativeHeat069Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat069Pass12]
  have h16 : nativeHeatPasses nativeGap070Old nativeHeat069Frames nativeHeat069Coef nativeHeat069Fixed nativeHeat069Base 16 nativeHeat069Y00 = nativeHeat069Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat069Pass16]
  have h20 : nativeHeatPasses nativeGap070Old nativeHeat069Frames nativeHeat069Coef nativeHeat069Fixed nativeHeat069Base 20 nativeHeat069Y00 = nativeHeat069Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat069Pass20]
  have h24 : nativeHeatPasses nativeGap070Old nativeHeat069Frames nativeHeat069Coef nativeHeat069Fixed nativeHeat069Base 24 nativeHeat069Y00 = nativeHeat069Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat069Pass24]
  have h28 : nativeHeatPasses nativeGap070Old nativeHeat069Frames nativeHeat069Coef nativeHeat069Fixed nativeHeat069Base 28 nativeHeat069Y00 = nativeHeat069Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat069Pass28]
  have h32 : nativeHeatPasses nativeGap070Old nativeHeat069Frames nativeHeat069Coef nativeHeat069Fixed nativeHeat069Base 32 nativeHeat069Y00 = nativeHeat069Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat069Pass32]
  have h36 : nativeHeatPasses nativeGap070Old nativeHeat069Frames nativeHeat069Coef nativeHeat069Fixed nativeHeat069Base 36 nativeHeat069Y00 = nativeHeat069Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat069Pass36]
  have h40 : nativeHeatPasses nativeGap070Old nativeHeat069Frames nativeHeat069Coef nativeHeat069Fixed nativeHeat069Base 40 nativeHeat069Y00 = nativeHeat069Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat069Pass40]
  have h44 : nativeHeatPasses nativeGap070Old nativeHeat069Frames nativeHeat069Coef nativeHeat069Fixed nativeHeat069Base 44 nativeHeat069Y00 = nativeHeat069Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat069Pass44]
  have h48 : nativeHeatPasses nativeGap070Old nativeHeat069Frames nativeHeat069Coef nativeHeat069Fixed nativeHeat069Base 48 nativeHeat069Y00 = nativeHeat069Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat069Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
