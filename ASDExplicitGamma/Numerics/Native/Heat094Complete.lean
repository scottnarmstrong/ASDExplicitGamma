module
public import ASDExplicitGamma.Numerics.Native.Heat094Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat094Y00_formula : nativeHeat094Y00 = nativeHeat094Frames.y := by
  decide +kernel

theorem nativeHeat094All48 : nativeHeatPasses nativeGap095Old nativeHeat094Frames nativeHeat094Coef nativeHeat094Fixed nativeHeat094Base 48 nativeHeat094Frames.y = nativeHeat094Y48 := by
  rw [← nativeHeat094Y00_formula]
  have h4 : nativeHeatPasses nativeGap095Old nativeHeat094Frames nativeHeat094Coef nativeHeat094Fixed nativeHeat094Base 4 nativeHeat094Y00 = nativeHeat094Y04 := nativeHeat094Pass04
  have h8 : nativeHeatPasses nativeGap095Old nativeHeat094Frames nativeHeat094Coef nativeHeat094Fixed nativeHeat094Base 8 nativeHeat094Y00 = nativeHeat094Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat094Pass08]
  have h12 : nativeHeatPasses nativeGap095Old nativeHeat094Frames nativeHeat094Coef nativeHeat094Fixed nativeHeat094Base 12 nativeHeat094Y00 = nativeHeat094Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat094Pass12]
  have h16 : nativeHeatPasses nativeGap095Old nativeHeat094Frames nativeHeat094Coef nativeHeat094Fixed nativeHeat094Base 16 nativeHeat094Y00 = nativeHeat094Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat094Pass16]
  have h20 : nativeHeatPasses nativeGap095Old nativeHeat094Frames nativeHeat094Coef nativeHeat094Fixed nativeHeat094Base 20 nativeHeat094Y00 = nativeHeat094Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat094Pass20]
  have h24 : nativeHeatPasses nativeGap095Old nativeHeat094Frames nativeHeat094Coef nativeHeat094Fixed nativeHeat094Base 24 nativeHeat094Y00 = nativeHeat094Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat094Pass24]
  have h28 : nativeHeatPasses nativeGap095Old nativeHeat094Frames nativeHeat094Coef nativeHeat094Fixed nativeHeat094Base 28 nativeHeat094Y00 = nativeHeat094Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat094Pass28]
  have h32 : nativeHeatPasses nativeGap095Old nativeHeat094Frames nativeHeat094Coef nativeHeat094Fixed nativeHeat094Base 32 nativeHeat094Y00 = nativeHeat094Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat094Pass32]
  have h36 : nativeHeatPasses nativeGap095Old nativeHeat094Frames nativeHeat094Coef nativeHeat094Fixed nativeHeat094Base 36 nativeHeat094Y00 = nativeHeat094Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat094Pass36]
  have h40 : nativeHeatPasses nativeGap095Old nativeHeat094Frames nativeHeat094Coef nativeHeat094Fixed nativeHeat094Base 40 nativeHeat094Y00 = nativeHeat094Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat094Pass40]
  have h44 : nativeHeatPasses nativeGap095Old nativeHeat094Frames nativeHeat094Coef nativeHeat094Fixed nativeHeat094Base 44 nativeHeat094Y00 = nativeHeat094Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat094Pass44]
  have h48 : nativeHeatPasses nativeGap095Old nativeHeat094Frames nativeHeat094Coef nativeHeat094Fixed nativeHeat094Base 48 nativeHeat094Y00 = nativeHeat094Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat094Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
