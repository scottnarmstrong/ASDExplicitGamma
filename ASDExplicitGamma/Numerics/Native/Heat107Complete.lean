module
public import ASDExplicitGamma.Numerics.Native.Heat107Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat107Y00_formula : nativeHeat107Y00 = nativeHeat107Frames.y := by
  decide +kernel

theorem nativeHeat107All48 : nativeHeatPasses nativeGap108Old nativeHeat107Frames nativeHeat107Coef nativeHeat107Fixed nativeHeat107Base 48 nativeHeat107Frames.y = nativeHeat107Y48 := by
  rw [← nativeHeat107Y00_formula]
  have h4 : nativeHeatPasses nativeGap108Old nativeHeat107Frames nativeHeat107Coef nativeHeat107Fixed nativeHeat107Base 4 nativeHeat107Y00 = nativeHeat107Y04 := nativeHeat107Pass04
  have h8 : nativeHeatPasses nativeGap108Old nativeHeat107Frames nativeHeat107Coef nativeHeat107Fixed nativeHeat107Base 8 nativeHeat107Y00 = nativeHeat107Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat107Pass08]
  have h12 : nativeHeatPasses nativeGap108Old nativeHeat107Frames nativeHeat107Coef nativeHeat107Fixed nativeHeat107Base 12 nativeHeat107Y00 = nativeHeat107Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat107Pass12]
  have h16 : nativeHeatPasses nativeGap108Old nativeHeat107Frames nativeHeat107Coef nativeHeat107Fixed nativeHeat107Base 16 nativeHeat107Y00 = nativeHeat107Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat107Pass16]
  have h20 : nativeHeatPasses nativeGap108Old nativeHeat107Frames nativeHeat107Coef nativeHeat107Fixed nativeHeat107Base 20 nativeHeat107Y00 = nativeHeat107Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat107Pass20]
  have h24 : nativeHeatPasses nativeGap108Old nativeHeat107Frames nativeHeat107Coef nativeHeat107Fixed nativeHeat107Base 24 nativeHeat107Y00 = nativeHeat107Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat107Pass24]
  have h28 : nativeHeatPasses nativeGap108Old nativeHeat107Frames nativeHeat107Coef nativeHeat107Fixed nativeHeat107Base 28 nativeHeat107Y00 = nativeHeat107Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat107Pass28]
  have h32 : nativeHeatPasses nativeGap108Old nativeHeat107Frames nativeHeat107Coef nativeHeat107Fixed nativeHeat107Base 32 nativeHeat107Y00 = nativeHeat107Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat107Pass32]
  have h36 : nativeHeatPasses nativeGap108Old nativeHeat107Frames nativeHeat107Coef nativeHeat107Fixed nativeHeat107Base 36 nativeHeat107Y00 = nativeHeat107Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat107Pass36]
  have h40 : nativeHeatPasses nativeGap108Old nativeHeat107Frames nativeHeat107Coef nativeHeat107Fixed nativeHeat107Base 40 nativeHeat107Y00 = nativeHeat107Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat107Pass40]
  have h44 : nativeHeatPasses nativeGap108Old nativeHeat107Frames nativeHeat107Coef nativeHeat107Fixed nativeHeat107Base 44 nativeHeat107Y00 = nativeHeat107Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat107Pass44]
  have h48 : nativeHeatPasses nativeGap108Old nativeHeat107Frames nativeHeat107Coef nativeHeat107Fixed nativeHeat107Base 48 nativeHeat107Y00 = nativeHeat107Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat107Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
