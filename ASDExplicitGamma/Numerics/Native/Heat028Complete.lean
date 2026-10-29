module
public import ASDExplicitGamma.Numerics.Native.Heat028Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat028Y00_formula : nativeHeat028Y00 = nativeHeat028Frames.y := by
  decide +kernel

theorem nativeHeat028All48 : nativeHeatPasses nativeGap029Old nativeHeat028Frames nativeHeat028Coef nativeHeat028Fixed nativeHeat028Base 48 nativeHeat028Frames.y = nativeHeat028Y48 := by
  rw [← nativeHeat028Y00_formula]
  have h4 : nativeHeatPasses nativeGap029Old nativeHeat028Frames nativeHeat028Coef nativeHeat028Fixed nativeHeat028Base 4 nativeHeat028Y00 = nativeHeat028Y04 := nativeHeat028Pass04
  have h8 : nativeHeatPasses nativeGap029Old nativeHeat028Frames nativeHeat028Coef nativeHeat028Fixed nativeHeat028Base 8 nativeHeat028Y00 = nativeHeat028Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat028Pass08]
  have h12 : nativeHeatPasses nativeGap029Old nativeHeat028Frames nativeHeat028Coef nativeHeat028Fixed nativeHeat028Base 12 nativeHeat028Y00 = nativeHeat028Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat028Pass12]
  have h16 : nativeHeatPasses nativeGap029Old nativeHeat028Frames nativeHeat028Coef nativeHeat028Fixed nativeHeat028Base 16 nativeHeat028Y00 = nativeHeat028Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat028Pass16]
  have h20 : nativeHeatPasses nativeGap029Old nativeHeat028Frames nativeHeat028Coef nativeHeat028Fixed nativeHeat028Base 20 nativeHeat028Y00 = nativeHeat028Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat028Pass20]
  have h24 : nativeHeatPasses nativeGap029Old nativeHeat028Frames nativeHeat028Coef nativeHeat028Fixed nativeHeat028Base 24 nativeHeat028Y00 = nativeHeat028Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat028Pass24]
  have h28 : nativeHeatPasses nativeGap029Old nativeHeat028Frames nativeHeat028Coef nativeHeat028Fixed nativeHeat028Base 28 nativeHeat028Y00 = nativeHeat028Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat028Pass28]
  have h32 : nativeHeatPasses nativeGap029Old nativeHeat028Frames nativeHeat028Coef nativeHeat028Fixed nativeHeat028Base 32 nativeHeat028Y00 = nativeHeat028Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat028Pass32]
  have h36 : nativeHeatPasses nativeGap029Old nativeHeat028Frames nativeHeat028Coef nativeHeat028Fixed nativeHeat028Base 36 nativeHeat028Y00 = nativeHeat028Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat028Pass36]
  have h40 : nativeHeatPasses nativeGap029Old nativeHeat028Frames nativeHeat028Coef nativeHeat028Fixed nativeHeat028Base 40 nativeHeat028Y00 = nativeHeat028Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat028Pass40]
  have h44 : nativeHeatPasses nativeGap029Old nativeHeat028Frames nativeHeat028Coef nativeHeat028Fixed nativeHeat028Base 44 nativeHeat028Y00 = nativeHeat028Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat028Pass44]
  have h48 : nativeHeatPasses nativeGap029Old nativeHeat028Frames nativeHeat028Coef nativeHeat028Fixed nativeHeat028Base 48 nativeHeat028Y00 = nativeHeat028Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat028Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
