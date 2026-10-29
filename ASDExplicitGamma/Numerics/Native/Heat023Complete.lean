module
public import ASDExplicitGamma.Numerics.Native.Heat023Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat023Y00_formula : nativeHeat023Y00 = nativeHeat023Frames.y := by
  decide +kernel

theorem nativeHeat023All48 : nativeHeatPasses nativeGap024Old nativeHeat023Frames nativeHeat023Coef nativeHeat023Fixed nativeHeat023Base 48 nativeHeat023Frames.y = nativeHeat023Y48 := by
  rw [← nativeHeat023Y00_formula]
  have h4 : nativeHeatPasses nativeGap024Old nativeHeat023Frames nativeHeat023Coef nativeHeat023Fixed nativeHeat023Base 4 nativeHeat023Y00 = nativeHeat023Y04 := nativeHeat023Pass04
  have h8 : nativeHeatPasses nativeGap024Old nativeHeat023Frames nativeHeat023Coef nativeHeat023Fixed nativeHeat023Base 8 nativeHeat023Y00 = nativeHeat023Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat023Pass08]
  have h12 : nativeHeatPasses nativeGap024Old nativeHeat023Frames nativeHeat023Coef nativeHeat023Fixed nativeHeat023Base 12 nativeHeat023Y00 = nativeHeat023Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat023Pass12]
  have h16 : nativeHeatPasses nativeGap024Old nativeHeat023Frames nativeHeat023Coef nativeHeat023Fixed nativeHeat023Base 16 nativeHeat023Y00 = nativeHeat023Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat023Pass16]
  have h20 : nativeHeatPasses nativeGap024Old nativeHeat023Frames nativeHeat023Coef nativeHeat023Fixed nativeHeat023Base 20 nativeHeat023Y00 = nativeHeat023Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat023Pass20]
  have h24 : nativeHeatPasses nativeGap024Old nativeHeat023Frames nativeHeat023Coef nativeHeat023Fixed nativeHeat023Base 24 nativeHeat023Y00 = nativeHeat023Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat023Pass24]
  have h28 : nativeHeatPasses nativeGap024Old nativeHeat023Frames nativeHeat023Coef nativeHeat023Fixed nativeHeat023Base 28 nativeHeat023Y00 = nativeHeat023Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat023Pass28]
  have h32 : nativeHeatPasses nativeGap024Old nativeHeat023Frames nativeHeat023Coef nativeHeat023Fixed nativeHeat023Base 32 nativeHeat023Y00 = nativeHeat023Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat023Pass32]
  have h36 : nativeHeatPasses nativeGap024Old nativeHeat023Frames nativeHeat023Coef nativeHeat023Fixed nativeHeat023Base 36 nativeHeat023Y00 = nativeHeat023Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat023Pass36]
  have h40 : nativeHeatPasses nativeGap024Old nativeHeat023Frames nativeHeat023Coef nativeHeat023Fixed nativeHeat023Base 40 nativeHeat023Y00 = nativeHeat023Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat023Pass40]
  have h44 : nativeHeatPasses nativeGap024Old nativeHeat023Frames nativeHeat023Coef nativeHeat023Fixed nativeHeat023Base 44 nativeHeat023Y00 = nativeHeat023Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat023Pass44]
  have h48 : nativeHeatPasses nativeGap024Old nativeHeat023Frames nativeHeat023Coef nativeHeat023Fixed nativeHeat023Base 48 nativeHeat023Y00 = nativeHeat023Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat023Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
