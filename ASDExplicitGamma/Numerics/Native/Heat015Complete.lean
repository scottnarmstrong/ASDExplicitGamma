module
public import ASDExplicitGamma.Numerics.Native.Heat015Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat015Y00_formula : nativeHeat015Y00 = nativeHeat015Frames.y := by
  decide +kernel

theorem nativeHeat015All48 : nativeHeatPasses nativeGap016Old nativeHeat015Frames nativeHeat015Coef nativeHeat015Fixed nativeHeat015Base 48 nativeHeat015Frames.y = nativeHeat015Y48 := by
  rw [← nativeHeat015Y00_formula]
  have h4 : nativeHeatPasses nativeGap016Old nativeHeat015Frames nativeHeat015Coef nativeHeat015Fixed nativeHeat015Base 4 nativeHeat015Y00 = nativeHeat015Y04 := nativeHeat015Pass04
  have h8 : nativeHeatPasses nativeGap016Old nativeHeat015Frames nativeHeat015Coef nativeHeat015Fixed nativeHeat015Base 8 nativeHeat015Y00 = nativeHeat015Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat015Pass08]
  have h12 : nativeHeatPasses nativeGap016Old nativeHeat015Frames nativeHeat015Coef nativeHeat015Fixed nativeHeat015Base 12 nativeHeat015Y00 = nativeHeat015Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat015Pass12]
  have h16 : nativeHeatPasses nativeGap016Old nativeHeat015Frames nativeHeat015Coef nativeHeat015Fixed nativeHeat015Base 16 nativeHeat015Y00 = nativeHeat015Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat015Pass16]
  have h20 : nativeHeatPasses nativeGap016Old nativeHeat015Frames nativeHeat015Coef nativeHeat015Fixed nativeHeat015Base 20 nativeHeat015Y00 = nativeHeat015Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat015Pass20]
  have h24 : nativeHeatPasses nativeGap016Old nativeHeat015Frames nativeHeat015Coef nativeHeat015Fixed nativeHeat015Base 24 nativeHeat015Y00 = nativeHeat015Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat015Pass24]
  have h28 : nativeHeatPasses nativeGap016Old nativeHeat015Frames nativeHeat015Coef nativeHeat015Fixed nativeHeat015Base 28 nativeHeat015Y00 = nativeHeat015Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat015Pass28]
  have h32 : nativeHeatPasses nativeGap016Old nativeHeat015Frames nativeHeat015Coef nativeHeat015Fixed nativeHeat015Base 32 nativeHeat015Y00 = nativeHeat015Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat015Pass32]
  have h36 : nativeHeatPasses nativeGap016Old nativeHeat015Frames nativeHeat015Coef nativeHeat015Fixed nativeHeat015Base 36 nativeHeat015Y00 = nativeHeat015Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat015Pass36]
  have h40 : nativeHeatPasses nativeGap016Old nativeHeat015Frames nativeHeat015Coef nativeHeat015Fixed nativeHeat015Base 40 nativeHeat015Y00 = nativeHeat015Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat015Pass40]
  have h44 : nativeHeatPasses nativeGap016Old nativeHeat015Frames nativeHeat015Coef nativeHeat015Fixed nativeHeat015Base 44 nativeHeat015Y00 = nativeHeat015Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat015Pass44]
  have h48 : nativeHeatPasses nativeGap016Old nativeHeat015Frames nativeHeat015Coef nativeHeat015Fixed nativeHeat015Base 48 nativeHeat015Y00 = nativeHeat015Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat015Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
