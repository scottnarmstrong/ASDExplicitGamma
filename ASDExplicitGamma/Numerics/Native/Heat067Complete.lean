module
public import ASDExplicitGamma.Numerics.Native.Heat067Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat067Y00_formula : nativeHeat067Y00 = nativeHeat067Frames.y := by
  decide +kernel

theorem nativeHeat067All48 : nativeHeatPasses nativeGap068Old nativeHeat067Frames nativeHeat067Coef nativeHeat067Fixed nativeHeat067Base 48 nativeHeat067Frames.y = nativeHeat067Y48 := by
  rw [← nativeHeat067Y00_formula]
  have h4 : nativeHeatPasses nativeGap068Old nativeHeat067Frames nativeHeat067Coef nativeHeat067Fixed nativeHeat067Base 4 nativeHeat067Y00 = nativeHeat067Y04 := nativeHeat067Pass04
  have h8 : nativeHeatPasses nativeGap068Old nativeHeat067Frames nativeHeat067Coef nativeHeat067Fixed nativeHeat067Base 8 nativeHeat067Y00 = nativeHeat067Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat067Pass08]
  have h12 : nativeHeatPasses nativeGap068Old nativeHeat067Frames nativeHeat067Coef nativeHeat067Fixed nativeHeat067Base 12 nativeHeat067Y00 = nativeHeat067Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat067Pass12]
  have h16 : nativeHeatPasses nativeGap068Old nativeHeat067Frames nativeHeat067Coef nativeHeat067Fixed nativeHeat067Base 16 nativeHeat067Y00 = nativeHeat067Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat067Pass16]
  have h20 : nativeHeatPasses nativeGap068Old nativeHeat067Frames nativeHeat067Coef nativeHeat067Fixed nativeHeat067Base 20 nativeHeat067Y00 = nativeHeat067Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat067Pass20]
  have h24 : nativeHeatPasses nativeGap068Old nativeHeat067Frames nativeHeat067Coef nativeHeat067Fixed nativeHeat067Base 24 nativeHeat067Y00 = nativeHeat067Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat067Pass24]
  have h28 : nativeHeatPasses nativeGap068Old nativeHeat067Frames nativeHeat067Coef nativeHeat067Fixed nativeHeat067Base 28 nativeHeat067Y00 = nativeHeat067Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat067Pass28]
  have h32 : nativeHeatPasses nativeGap068Old nativeHeat067Frames nativeHeat067Coef nativeHeat067Fixed nativeHeat067Base 32 nativeHeat067Y00 = nativeHeat067Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat067Pass32]
  have h36 : nativeHeatPasses nativeGap068Old nativeHeat067Frames nativeHeat067Coef nativeHeat067Fixed nativeHeat067Base 36 nativeHeat067Y00 = nativeHeat067Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat067Pass36]
  have h40 : nativeHeatPasses nativeGap068Old nativeHeat067Frames nativeHeat067Coef nativeHeat067Fixed nativeHeat067Base 40 nativeHeat067Y00 = nativeHeat067Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat067Pass40]
  have h44 : nativeHeatPasses nativeGap068Old nativeHeat067Frames nativeHeat067Coef nativeHeat067Fixed nativeHeat067Base 44 nativeHeat067Y00 = nativeHeat067Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat067Pass44]
  have h48 : nativeHeatPasses nativeGap068Old nativeHeat067Frames nativeHeat067Coef nativeHeat067Fixed nativeHeat067Base 48 nativeHeat067Y00 = nativeHeat067Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat067Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
