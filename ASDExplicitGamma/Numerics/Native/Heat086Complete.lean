module
public import ASDExplicitGamma.Numerics.Native.Heat086Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat086Y00_formula : nativeHeat086Y00 = nativeHeat086Frames.y := by
  decide +kernel

theorem nativeHeat086All48 : nativeHeatPasses nativeGap087Old nativeHeat086Frames nativeHeat086Coef nativeHeat086Fixed nativeHeat086Base 48 nativeHeat086Frames.y = nativeHeat086Y48 := by
  rw [← nativeHeat086Y00_formula]
  have h4 : nativeHeatPasses nativeGap087Old nativeHeat086Frames nativeHeat086Coef nativeHeat086Fixed nativeHeat086Base 4 nativeHeat086Y00 = nativeHeat086Y04 := nativeHeat086Pass04
  have h8 : nativeHeatPasses nativeGap087Old nativeHeat086Frames nativeHeat086Coef nativeHeat086Fixed nativeHeat086Base 8 nativeHeat086Y00 = nativeHeat086Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat086Pass08]
  have h12 : nativeHeatPasses nativeGap087Old nativeHeat086Frames nativeHeat086Coef nativeHeat086Fixed nativeHeat086Base 12 nativeHeat086Y00 = nativeHeat086Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat086Pass12]
  have h16 : nativeHeatPasses nativeGap087Old nativeHeat086Frames nativeHeat086Coef nativeHeat086Fixed nativeHeat086Base 16 nativeHeat086Y00 = nativeHeat086Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat086Pass16]
  have h20 : nativeHeatPasses nativeGap087Old nativeHeat086Frames nativeHeat086Coef nativeHeat086Fixed nativeHeat086Base 20 nativeHeat086Y00 = nativeHeat086Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat086Pass20]
  have h24 : nativeHeatPasses nativeGap087Old nativeHeat086Frames nativeHeat086Coef nativeHeat086Fixed nativeHeat086Base 24 nativeHeat086Y00 = nativeHeat086Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat086Pass24]
  have h28 : nativeHeatPasses nativeGap087Old nativeHeat086Frames nativeHeat086Coef nativeHeat086Fixed nativeHeat086Base 28 nativeHeat086Y00 = nativeHeat086Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat086Pass28]
  have h32 : nativeHeatPasses nativeGap087Old nativeHeat086Frames nativeHeat086Coef nativeHeat086Fixed nativeHeat086Base 32 nativeHeat086Y00 = nativeHeat086Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat086Pass32]
  have h36 : nativeHeatPasses nativeGap087Old nativeHeat086Frames nativeHeat086Coef nativeHeat086Fixed nativeHeat086Base 36 nativeHeat086Y00 = nativeHeat086Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat086Pass36]
  have h40 : nativeHeatPasses nativeGap087Old nativeHeat086Frames nativeHeat086Coef nativeHeat086Fixed nativeHeat086Base 40 nativeHeat086Y00 = nativeHeat086Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat086Pass40]
  have h44 : nativeHeatPasses nativeGap087Old nativeHeat086Frames nativeHeat086Coef nativeHeat086Fixed nativeHeat086Base 44 nativeHeat086Y00 = nativeHeat086Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat086Pass44]
  have h48 : nativeHeatPasses nativeGap087Old nativeHeat086Frames nativeHeat086Coef nativeHeat086Fixed nativeHeat086Base 48 nativeHeat086Y00 = nativeHeat086Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat086Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
