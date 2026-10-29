module
public import ASDExplicitGamma.Numerics.Native.Heat025Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat025Y00_formula : nativeHeat025Y00 = nativeHeat025Frames.y := by
  decide +kernel

theorem nativeHeat025All48 : nativeHeatPasses nativeGap026Old nativeHeat025Frames nativeHeat025Coef nativeHeat025Fixed nativeHeat025Base 48 nativeHeat025Frames.y = nativeHeat025Y48 := by
  rw [← nativeHeat025Y00_formula]
  have h4 : nativeHeatPasses nativeGap026Old nativeHeat025Frames nativeHeat025Coef nativeHeat025Fixed nativeHeat025Base 4 nativeHeat025Y00 = nativeHeat025Y04 := nativeHeat025Pass04
  have h8 : nativeHeatPasses nativeGap026Old nativeHeat025Frames nativeHeat025Coef nativeHeat025Fixed nativeHeat025Base 8 nativeHeat025Y00 = nativeHeat025Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat025Pass08]
  have h12 : nativeHeatPasses nativeGap026Old nativeHeat025Frames nativeHeat025Coef nativeHeat025Fixed nativeHeat025Base 12 nativeHeat025Y00 = nativeHeat025Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat025Pass12]
  have h16 : nativeHeatPasses nativeGap026Old nativeHeat025Frames nativeHeat025Coef nativeHeat025Fixed nativeHeat025Base 16 nativeHeat025Y00 = nativeHeat025Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat025Pass16]
  have h20 : nativeHeatPasses nativeGap026Old nativeHeat025Frames nativeHeat025Coef nativeHeat025Fixed nativeHeat025Base 20 nativeHeat025Y00 = nativeHeat025Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat025Pass20]
  have h24 : nativeHeatPasses nativeGap026Old nativeHeat025Frames nativeHeat025Coef nativeHeat025Fixed nativeHeat025Base 24 nativeHeat025Y00 = nativeHeat025Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat025Pass24]
  have h28 : nativeHeatPasses nativeGap026Old nativeHeat025Frames nativeHeat025Coef nativeHeat025Fixed nativeHeat025Base 28 nativeHeat025Y00 = nativeHeat025Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat025Pass28]
  have h32 : nativeHeatPasses nativeGap026Old nativeHeat025Frames nativeHeat025Coef nativeHeat025Fixed nativeHeat025Base 32 nativeHeat025Y00 = nativeHeat025Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat025Pass32]
  have h36 : nativeHeatPasses nativeGap026Old nativeHeat025Frames nativeHeat025Coef nativeHeat025Fixed nativeHeat025Base 36 nativeHeat025Y00 = nativeHeat025Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat025Pass36]
  have h40 : nativeHeatPasses nativeGap026Old nativeHeat025Frames nativeHeat025Coef nativeHeat025Fixed nativeHeat025Base 40 nativeHeat025Y00 = nativeHeat025Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat025Pass40]
  have h44 : nativeHeatPasses nativeGap026Old nativeHeat025Frames nativeHeat025Coef nativeHeat025Fixed nativeHeat025Base 44 nativeHeat025Y00 = nativeHeat025Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat025Pass44]
  have h48 : nativeHeatPasses nativeGap026Old nativeHeat025Frames nativeHeat025Coef nativeHeat025Fixed nativeHeat025Base 48 nativeHeat025Y00 = nativeHeat025Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat025Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
