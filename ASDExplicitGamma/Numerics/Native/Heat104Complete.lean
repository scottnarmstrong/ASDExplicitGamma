module
public import ASDExplicitGamma.Numerics.Native.Heat104Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat104Y00_formula : nativeHeat104Y00 = nativeHeat104Frames.y := by
  decide +kernel

theorem nativeHeat104All48 : nativeHeatPasses nativeGap105Old nativeHeat104Frames nativeHeat104Coef nativeHeat104Fixed nativeHeat104Base 48 nativeHeat104Frames.y = nativeHeat104Y48 := by
  rw [← nativeHeat104Y00_formula]
  have h4 : nativeHeatPasses nativeGap105Old nativeHeat104Frames nativeHeat104Coef nativeHeat104Fixed nativeHeat104Base 4 nativeHeat104Y00 = nativeHeat104Y04 := nativeHeat104Pass04
  have h8 : nativeHeatPasses nativeGap105Old nativeHeat104Frames nativeHeat104Coef nativeHeat104Fixed nativeHeat104Base 8 nativeHeat104Y00 = nativeHeat104Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat104Pass08]
  have h12 : nativeHeatPasses nativeGap105Old nativeHeat104Frames nativeHeat104Coef nativeHeat104Fixed nativeHeat104Base 12 nativeHeat104Y00 = nativeHeat104Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat104Pass12]
  have h16 : nativeHeatPasses nativeGap105Old nativeHeat104Frames nativeHeat104Coef nativeHeat104Fixed nativeHeat104Base 16 nativeHeat104Y00 = nativeHeat104Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat104Pass16]
  have h20 : nativeHeatPasses nativeGap105Old nativeHeat104Frames nativeHeat104Coef nativeHeat104Fixed nativeHeat104Base 20 nativeHeat104Y00 = nativeHeat104Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat104Pass20]
  have h24 : nativeHeatPasses nativeGap105Old nativeHeat104Frames nativeHeat104Coef nativeHeat104Fixed nativeHeat104Base 24 nativeHeat104Y00 = nativeHeat104Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat104Pass24]
  have h28 : nativeHeatPasses nativeGap105Old nativeHeat104Frames nativeHeat104Coef nativeHeat104Fixed nativeHeat104Base 28 nativeHeat104Y00 = nativeHeat104Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat104Pass28]
  have h32 : nativeHeatPasses nativeGap105Old nativeHeat104Frames nativeHeat104Coef nativeHeat104Fixed nativeHeat104Base 32 nativeHeat104Y00 = nativeHeat104Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat104Pass32]
  have h36 : nativeHeatPasses nativeGap105Old nativeHeat104Frames nativeHeat104Coef nativeHeat104Fixed nativeHeat104Base 36 nativeHeat104Y00 = nativeHeat104Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat104Pass36]
  have h40 : nativeHeatPasses nativeGap105Old nativeHeat104Frames nativeHeat104Coef nativeHeat104Fixed nativeHeat104Base 40 nativeHeat104Y00 = nativeHeat104Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat104Pass40]
  have h44 : nativeHeatPasses nativeGap105Old nativeHeat104Frames nativeHeat104Coef nativeHeat104Fixed nativeHeat104Base 44 nativeHeat104Y00 = nativeHeat104Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat104Pass44]
  have h48 : nativeHeatPasses nativeGap105Old nativeHeat104Frames nativeHeat104Coef nativeHeat104Fixed nativeHeat104Base 48 nativeHeat104Y00 = nativeHeat104Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat104Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
