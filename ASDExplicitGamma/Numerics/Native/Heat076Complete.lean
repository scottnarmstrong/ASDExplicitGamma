module
public import ASDExplicitGamma.Numerics.Native.Heat076Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat076Y00_formula : nativeHeat076Y00 = nativeHeat076Frames.y := by
  decide +kernel

theorem nativeHeat076All48 : nativeHeatPasses nativeGap077Old nativeHeat076Frames nativeHeat076Coef nativeHeat076Fixed nativeHeat076Base 48 nativeHeat076Frames.y = nativeHeat076Y48 := by
  rw [← nativeHeat076Y00_formula]
  have h4 : nativeHeatPasses nativeGap077Old nativeHeat076Frames nativeHeat076Coef nativeHeat076Fixed nativeHeat076Base 4 nativeHeat076Y00 = nativeHeat076Y04 := nativeHeat076Pass04
  have h8 : nativeHeatPasses nativeGap077Old nativeHeat076Frames nativeHeat076Coef nativeHeat076Fixed nativeHeat076Base 8 nativeHeat076Y00 = nativeHeat076Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat076Pass08]
  have h12 : nativeHeatPasses nativeGap077Old nativeHeat076Frames nativeHeat076Coef nativeHeat076Fixed nativeHeat076Base 12 nativeHeat076Y00 = nativeHeat076Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat076Pass12]
  have h16 : nativeHeatPasses nativeGap077Old nativeHeat076Frames nativeHeat076Coef nativeHeat076Fixed nativeHeat076Base 16 nativeHeat076Y00 = nativeHeat076Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat076Pass16]
  have h20 : nativeHeatPasses nativeGap077Old nativeHeat076Frames nativeHeat076Coef nativeHeat076Fixed nativeHeat076Base 20 nativeHeat076Y00 = nativeHeat076Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat076Pass20]
  have h24 : nativeHeatPasses nativeGap077Old nativeHeat076Frames nativeHeat076Coef nativeHeat076Fixed nativeHeat076Base 24 nativeHeat076Y00 = nativeHeat076Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat076Pass24]
  have h28 : nativeHeatPasses nativeGap077Old nativeHeat076Frames nativeHeat076Coef nativeHeat076Fixed nativeHeat076Base 28 nativeHeat076Y00 = nativeHeat076Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat076Pass28]
  have h32 : nativeHeatPasses nativeGap077Old nativeHeat076Frames nativeHeat076Coef nativeHeat076Fixed nativeHeat076Base 32 nativeHeat076Y00 = nativeHeat076Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat076Pass32]
  have h36 : nativeHeatPasses nativeGap077Old nativeHeat076Frames nativeHeat076Coef nativeHeat076Fixed nativeHeat076Base 36 nativeHeat076Y00 = nativeHeat076Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat076Pass36]
  have h40 : nativeHeatPasses nativeGap077Old nativeHeat076Frames nativeHeat076Coef nativeHeat076Fixed nativeHeat076Base 40 nativeHeat076Y00 = nativeHeat076Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat076Pass40]
  have h44 : nativeHeatPasses nativeGap077Old nativeHeat076Frames nativeHeat076Coef nativeHeat076Fixed nativeHeat076Base 44 nativeHeat076Y00 = nativeHeat076Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat076Pass44]
  have h48 : nativeHeatPasses nativeGap077Old nativeHeat076Frames nativeHeat076Coef nativeHeat076Fixed nativeHeat076Base 48 nativeHeat076Y00 = nativeHeat076Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat076Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
