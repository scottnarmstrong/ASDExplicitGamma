module
public import ASDExplicitGamma.Numerics.Native.Heat030Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat030Y00_formula : nativeHeat030Y00 = nativeHeat030Frames.y := by
  decide +kernel

theorem nativeHeat030All48 : nativeHeatPasses nativeGap031Old nativeHeat030Frames nativeHeat030Coef nativeHeat030Fixed nativeHeat030Base 48 nativeHeat030Frames.y = nativeHeat030Y48 := by
  rw [← nativeHeat030Y00_formula]
  have h4 : nativeHeatPasses nativeGap031Old nativeHeat030Frames nativeHeat030Coef nativeHeat030Fixed nativeHeat030Base 4 nativeHeat030Y00 = nativeHeat030Y04 := nativeHeat030Pass04
  have h8 : nativeHeatPasses nativeGap031Old nativeHeat030Frames nativeHeat030Coef nativeHeat030Fixed nativeHeat030Base 8 nativeHeat030Y00 = nativeHeat030Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat030Pass08]
  have h12 : nativeHeatPasses nativeGap031Old nativeHeat030Frames nativeHeat030Coef nativeHeat030Fixed nativeHeat030Base 12 nativeHeat030Y00 = nativeHeat030Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat030Pass12]
  have h16 : nativeHeatPasses nativeGap031Old nativeHeat030Frames nativeHeat030Coef nativeHeat030Fixed nativeHeat030Base 16 nativeHeat030Y00 = nativeHeat030Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat030Pass16]
  have h20 : nativeHeatPasses nativeGap031Old nativeHeat030Frames nativeHeat030Coef nativeHeat030Fixed nativeHeat030Base 20 nativeHeat030Y00 = nativeHeat030Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat030Pass20]
  have h24 : nativeHeatPasses nativeGap031Old nativeHeat030Frames nativeHeat030Coef nativeHeat030Fixed nativeHeat030Base 24 nativeHeat030Y00 = nativeHeat030Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat030Pass24]
  have h28 : nativeHeatPasses nativeGap031Old nativeHeat030Frames nativeHeat030Coef nativeHeat030Fixed nativeHeat030Base 28 nativeHeat030Y00 = nativeHeat030Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat030Pass28]
  have h32 : nativeHeatPasses nativeGap031Old nativeHeat030Frames nativeHeat030Coef nativeHeat030Fixed nativeHeat030Base 32 nativeHeat030Y00 = nativeHeat030Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat030Pass32]
  have h36 : nativeHeatPasses nativeGap031Old nativeHeat030Frames nativeHeat030Coef nativeHeat030Fixed nativeHeat030Base 36 nativeHeat030Y00 = nativeHeat030Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat030Pass36]
  have h40 : nativeHeatPasses nativeGap031Old nativeHeat030Frames nativeHeat030Coef nativeHeat030Fixed nativeHeat030Base 40 nativeHeat030Y00 = nativeHeat030Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat030Pass40]
  have h44 : nativeHeatPasses nativeGap031Old nativeHeat030Frames nativeHeat030Coef nativeHeat030Fixed nativeHeat030Base 44 nativeHeat030Y00 = nativeHeat030Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat030Pass44]
  have h48 : nativeHeatPasses nativeGap031Old nativeHeat030Frames nativeHeat030Coef nativeHeat030Fixed nativeHeat030Base 48 nativeHeat030Y00 = nativeHeat030Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat030Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
