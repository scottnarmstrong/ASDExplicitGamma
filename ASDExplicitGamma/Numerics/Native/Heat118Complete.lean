module
public import ASDExplicitGamma.Numerics.Native.Heat118Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat118Y00_formula : nativeHeat118Y00 = nativeHeat118Frames.y := by
  decide +kernel

theorem nativeHeat118All48 : nativeHeatPasses nativeGap119Old nativeHeat118Frames nativeHeat118Coef nativeHeat118Fixed nativeHeat118Base 48 nativeHeat118Frames.y = nativeHeat118Y48 := by
  rw [← nativeHeat118Y00_formula]
  have h4 : nativeHeatPasses nativeGap119Old nativeHeat118Frames nativeHeat118Coef nativeHeat118Fixed nativeHeat118Base 4 nativeHeat118Y00 = nativeHeat118Y04 := nativeHeat118Pass04
  have h8 : nativeHeatPasses nativeGap119Old nativeHeat118Frames nativeHeat118Coef nativeHeat118Fixed nativeHeat118Base 8 nativeHeat118Y00 = nativeHeat118Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat118Pass08]
  have h12 : nativeHeatPasses nativeGap119Old nativeHeat118Frames nativeHeat118Coef nativeHeat118Fixed nativeHeat118Base 12 nativeHeat118Y00 = nativeHeat118Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat118Pass12]
  have h16 : nativeHeatPasses nativeGap119Old nativeHeat118Frames nativeHeat118Coef nativeHeat118Fixed nativeHeat118Base 16 nativeHeat118Y00 = nativeHeat118Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat118Pass16]
  have h20 : nativeHeatPasses nativeGap119Old nativeHeat118Frames nativeHeat118Coef nativeHeat118Fixed nativeHeat118Base 20 nativeHeat118Y00 = nativeHeat118Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat118Pass20]
  have h24 : nativeHeatPasses nativeGap119Old nativeHeat118Frames nativeHeat118Coef nativeHeat118Fixed nativeHeat118Base 24 nativeHeat118Y00 = nativeHeat118Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat118Pass24]
  have h28 : nativeHeatPasses nativeGap119Old nativeHeat118Frames nativeHeat118Coef nativeHeat118Fixed nativeHeat118Base 28 nativeHeat118Y00 = nativeHeat118Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat118Pass28]
  have h32 : nativeHeatPasses nativeGap119Old nativeHeat118Frames nativeHeat118Coef nativeHeat118Fixed nativeHeat118Base 32 nativeHeat118Y00 = nativeHeat118Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat118Pass32]
  have h36 : nativeHeatPasses nativeGap119Old nativeHeat118Frames nativeHeat118Coef nativeHeat118Fixed nativeHeat118Base 36 nativeHeat118Y00 = nativeHeat118Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat118Pass36]
  have h40 : nativeHeatPasses nativeGap119Old nativeHeat118Frames nativeHeat118Coef nativeHeat118Fixed nativeHeat118Base 40 nativeHeat118Y00 = nativeHeat118Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat118Pass40]
  have h44 : nativeHeatPasses nativeGap119Old nativeHeat118Frames nativeHeat118Coef nativeHeat118Fixed nativeHeat118Base 44 nativeHeat118Y00 = nativeHeat118Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat118Pass44]
  have h48 : nativeHeatPasses nativeGap119Old nativeHeat118Frames nativeHeat118Coef nativeHeat118Fixed nativeHeat118Base 48 nativeHeat118Y00 = nativeHeat118Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat118Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
