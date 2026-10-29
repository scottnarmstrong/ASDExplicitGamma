module
public import ASDExplicitGamma.Numerics.Native.Heat140Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat140Y00_formula : nativeHeat140Y00 = nativeHeat140Frames.y := by
  decide +kernel

theorem nativeHeat140All48 : nativeHeatPasses nativeGap141Old nativeHeat140Frames nativeHeat140Coef nativeHeat140Fixed nativeHeat140Base 48 nativeHeat140Frames.y = nativeHeat140Y48 := by
  rw [← nativeHeat140Y00_formula]
  have h4 : nativeHeatPasses nativeGap141Old nativeHeat140Frames nativeHeat140Coef nativeHeat140Fixed nativeHeat140Base 4 nativeHeat140Y00 = nativeHeat140Y04 := nativeHeat140Pass04
  have h8 : nativeHeatPasses nativeGap141Old nativeHeat140Frames nativeHeat140Coef nativeHeat140Fixed nativeHeat140Base 8 nativeHeat140Y00 = nativeHeat140Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat140Pass08]
  have h12 : nativeHeatPasses nativeGap141Old nativeHeat140Frames nativeHeat140Coef nativeHeat140Fixed nativeHeat140Base 12 nativeHeat140Y00 = nativeHeat140Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat140Pass12]
  have h16 : nativeHeatPasses nativeGap141Old nativeHeat140Frames nativeHeat140Coef nativeHeat140Fixed nativeHeat140Base 16 nativeHeat140Y00 = nativeHeat140Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat140Pass16]
  have h20 : nativeHeatPasses nativeGap141Old nativeHeat140Frames nativeHeat140Coef nativeHeat140Fixed nativeHeat140Base 20 nativeHeat140Y00 = nativeHeat140Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat140Pass20]
  have h24 : nativeHeatPasses nativeGap141Old nativeHeat140Frames nativeHeat140Coef nativeHeat140Fixed nativeHeat140Base 24 nativeHeat140Y00 = nativeHeat140Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat140Pass24]
  have h28 : nativeHeatPasses nativeGap141Old nativeHeat140Frames nativeHeat140Coef nativeHeat140Fixed nativeHeat140Base 28 nativeHeat140Y00 = nativeHeat140Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat140Pass28]
  have h32 : nativeHeatPasses nativeGap141Old nativeHeat140Frames nativeHeat140Coef nativeHeat140Fixed nativeHeat140Base 32 nativeHeat140Y00 = nativeHeat140Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat140Pass32]
  have h36 : nativeHeatPasses nativeGap141Old nativeHeat140Frames nativeHeat140Coef nativeHeat140Fixed nativeHeat140Base 36 nativeHeat140Y00 = nativeHeat140Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat140Pass36]
  have h40 : nativeHeatPasses nativeGap141Old nativeHeat140Frames nativeHeat140Coef nativeHeat140Fixed nativeHeat140Base 40 nativeHeat140Y00 = nativeHeat140Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat140Pass40]
  have h44 : nativeHeatPasses nativeGap141Old nativeHeat140Frames nativeHeat140Coef nativeHeat140Fixed nativeHeat140Base 44 nativeHeat140Y00 = nativeHeat140Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat140Pass44]
  have h48 : nativeHeatPasses nativeGap141Old nativeHeat140Frames nativeHeat140Coef nativeHeat140Fixed nativeHeat140Base 48 nativeHeat140Y00 = nativeHeat140Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat140Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
