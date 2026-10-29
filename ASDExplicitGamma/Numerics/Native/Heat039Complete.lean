module
public import ASDExplicitGamma.Numerics.Native.Heat039Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat039Y00_formula : nativeHeat039Y00 = nativeHeat039Frames.y := by
  decide +kernel

theorem nativeHeat039All48 : nativeHeatPasses nativeGap040Old nativeHeat039Frames nativeHeat039Coef nativeHeat039Fixed nativeHeat039Base 48 nativeHeat039Frames.y = nativeHeat039Y48 := by
  rw [← nativeHeat039Y00_formula]
  have h4 : nativeHeatPasses nativeGap040Old nativeHeat039Frames nativeHeat039Coef nativeHeat039Fixed nativeHeat039Base 4 nativeHeat039Y00 = nativeHeat039Y04 := nativeHeat039Pass04
  have h8 : nativeHeatPasses nativeGap040Old nativeHeat039Frames nativeHeat039Coef nativeHeat039Fixed nativeHeat039Base 8 nativeHeat039Y00 = nativeHeat039Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat039Pass08]
  have h12 : nativeHeatPasses nativeGap040Old nativeHeat039Frames nativeHeat039Coef nativeHeat039Fixed nativeHeat039Base 12 nativeHeat039Y00 = nativeHeat039Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat039Pass12]
  have h16 : nativeHeatPasses nativeGap040Old nativeHeat039Frames nativeHeat039Coef nativeHeat039Fixed nativeHeat039Base 16 nativeHeat039Y00 = nativeHeat039Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat039Pass16]
  have h20 : nativeHeatPasses nativeGap040Old nativeHeat039Frames nativeHeat039Coef nativeHeat039Fixed nativeHeat039Base 20 nativeHeat039Y00 = nativeHeat039Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat039Pass20]
  have h24 : nativeHeatPasses nativeGap040Old nativeHeat039Frames nativeHeat039Coef nativeHeat039Fixed nativeHeat039Base 24 nativeHeat039Y00 = nativeHeat039Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat039Pass24]
  have h28 : nativeHeatPasses nativeGap040Old nativeHeat039Frames nativeHeat039Coef nativeHeat039Fixed nativeHeat039Base 28 nativeHeat039Y00 = nativeHeat039Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat039Pass28]
  have h32 : nativeHeatPasses nativeGap040Old nativeHeat039Frames nativeHeat039Coef nativeHeat039Fixed nativeHeat039Base 32 nativeHeat039Y00 = nativeHeat039Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat039Pass32]
  have h36 : nativeHeatPasses nativeGap040Old nativeHeat039Frames nativeHeat039Coef nativeHeat039Fixed nativeHeat039Base 36 nativeHeat039Y00 = nativeHeat039Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat039Pass36]
  have h40 : nativeHeatPasses nativeGap040Old nativeHeat039Frames nativeHeat039Coef nativeHeat039Fixed nativeHeat039Base 40 nativeHeat039Y00 = nativeHeat039Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat039Pass40]
  have h44 : nativeHeatPasses nativeGap040Old nativeHeat039Frames nativeHeat039Coef nativeHeat039Fixed nativeHeat039Base 44 nativeHeat039Y00 = nativeHeat039Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat039Pass44]
  have h48 : nativeHeatPasses nativeGap040Old nativeHeat039Frames nativeHeat039Coef nativeHeat039Fixed nativeHeat039Base 48 nativeHeat039Y00 = nativeHeat039Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat039Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
