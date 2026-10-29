module
public import ASDExplicitGamma.Numerics.Native.Heat089Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat089Y00_formula : nativeHeat089Y00 = nativeHeat089Frames.y := by
  decide +kernel

theorem nativeHeat089All48 : nativeHeatPasses nativeGap090Old nativeHeat089Frames nativeHeat089Coef nativeHeat089Fixed nativeHeat089Base 48 nativeHeat089Frames.y = nativeHeat089Y48 := by
  rw [← nativeHeat089Y00_formula]
  have h4 : nativeHeatPasses nativeGap090Old nativeHeat089Frames nativeHeat089Coef nativeHeat089Fixed nativeHeat089Base 4 nativeHeat089Y00 = nativeHeat089Y04 := nativeHeat089Pass04
  have h8 : nativeHeatPasses nativeGap090Old nativeHeat089Frames nativeHeat089Coef nativeHeat089Fixed nativeHeat089Base 8 nativeHeat089Y00 = nativeHeat089Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat089Pass08]
  have h12 : nativeHeatPasses nativeGap090Old nativeHeat089Frames nativeHeat089Coef nativeHeat089Fixed nativeHeat089Base 12 nativeHeat089Y00 = nativeHeat089Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat089Pass12]
  have h16 : nativeHeatPasses nativeGap090Old nativeHeat089Frames nativeHeat089Coef nativeHeat089Fixed nativeHeat089Base 16 nativeHeat089Y00 = nativeHeat089Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat089Pass16]
  have h20 : nativeHeatPasses nativeGap090Old nativeHeat089Frames nativeHeat089Coef nativeHeat089Fixed nativeHeat089Base 20 nativeHeat089Y00 = nativeHeat089Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat089Pass20]
  have h24 : nativeHeatPasses nativeGap090Old nativeHeat089Frames nativeHeat089Coef nativeHeat089Fixed nativeHeat089Base 24 nativeHeat089Y00 = nativeHeat089Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat089Pass24]
  have h28 : nativeHeatPasses nativeGap090Old nativeHeat089Frames nativeHeat089Coef nativeHeat089Fixed nativeHeat089Base 28 nativeHeat089Y00 = nativeHeat089Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat089Pass28]
  have h32 : nativeHeatPasses nativeGap090Old nativeHeat089Frames nativeHeat089Coef nativeHeat089Fixed nativeHeat089Base 32 nativeHeat089Y00 = nativeHeat089Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat089Pass32]
  have h36 : nativeHeatPasses nativeGap090Old nativeHeat089Frames nativeHeat089Coef nativeHeat089Fixed nativeHeat089Base 36 nativeHeat089Y00 = nativeHeat089Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat089Pass36]
  have h40 : nativeHeatPasses nativeGap090Old nativeHeat089Frames nativeHeat089Coef nativeHeat089Fixed nativeHeat089Base 40 nativeHeat089Y00 = nativeHeat089Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat089Pass40]
  have h44 : nativeHeatPasses nativeGap090Old nativeHeat089Frames nativeHeat089Coef nativeHeat089Fixed nativeHeat089Base 44 nativeHeat089Y00 = nativeHeat089Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat089Pass44]
  have h48 : nativeHeatPasses nativeGap090Old nativeHeat089Frames nativeHeat089Coef nativeHeat089Fixed nativeHeat089Base 48 nativeHeat089Y00 = nativeHeat089Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat089Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
