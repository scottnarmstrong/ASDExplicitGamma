module
public import ASDExplicitGamma.Numerics.Native.Heat075Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat075Y00_formula : nativeHeat075Y00 = nativeHeat075Frames.y := by
  decide +kernel

theorem nativeHeat075All48 : nativeHeatPasses nativeGap076Old nativeHeat075Frames nativeHeat075Coef nativeHeat075Fixed nativeHeat075Base 48 nativeHeat075Frames.y = nativeHeat075Y48 := by
  rw [← nativeHeat075Y00_formula]
  have h4 : nativeHeatPasses nativeGap076Old nativeHeat075Frames nativeHeat075Coef nativeHeat075Fixed nativeHeat075Base 4 nativeHeat075Y00 = nativeHeat075Y04 := nativeHeat075Pass04
  have h8 : nativeHeatPasses nativeGap076Old nativeHeat075Frames nativeHeat075Coef nativeHeat075Fixed nativeHeat075Base 8 nativeHeat075Y00 = nativeHeat075Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat075Pass08]
  have h12 : nativeHeatPasses nativeGap076Old nativeHeat075Frames nativeHeat075Coef nativeHeat075Fixed nativeHeat075Base 12 nativeHeat075Y00 = nativeHeat075Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat075Pass12]
  have h16 : nativeHeatPasses nativeGap076Old nativeHeat075Frames nativeHeat075Coef nativeHeat075Fixed nativeHeat075Base 16 nativeHeat075Y00 = nativeHeat075Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat075Pass16]
  have h20 : nativeHeatPasses nativeGap076Old nativeHeat075Frames nativeHeat075Coef nativeHeat075Fixed nativeHeat075Base 20 nativeHeat075Y00 = nativeHeat075Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat075Pass20]
  have h24 : nativeHeatPasses nativeGap076Old nativeHeat075Frames nativeHeat075Coef nativeHeat075Fixed nativeHeat075Base 24 nativeHeat075Y00 = nativeHeat075Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat075Pass24]
  have h28 : nativeHeatPasses nativeGap076Old nativeHeat075Frames nativeHeat075Coef nativeHeat075Fixed nativeHeat075Base 28 nativeHeat075Y00 = nativeHeat075Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat075Pass28]
  have h32 : nativeHeatPasses nativeGap076Old nativeHeat075Frames nativeHeat075Coef nativeHeat075Fixed nativeHeat075Base 32 nativeHeat075Y00 = nativeHeat075Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat075Pass32]
  have h36 : nativeHeatPasses nativeGap076Old nativeHeat075Frames nativeHeat075Coef nativeHeat075Fixed nativeHeat075Base 36 nativeHeat075Y00 = nativeHeat075Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat075Pass36]
  have h40 : nativeHeatPasses nativeGap076Old nativeHeat075Frames nativeHeat075Coef nativeHeat075Fixed nativeHeat075Base 40 nativeHeat075Y00 = nativeHeat075Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat075Pass40]
  have h44 : nativeHeatPasses nativeGap076Old nativeHeat075Frames nativeHeat075Coef nativeHeat075Fixed nativeHeat075Base 44 nativeHeat075Y00 = nativeHeat075Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat075Pass44]
  have h48 : nativeHeatPasses nativeGap076Old nativeHeat075Frames nativeHeat075Coef nativeHeat075Fixed nativeHeat075Base 48 nativeHeat075Y00 = nativeHeat075Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat075Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
