module
public import ASDExplicitGamma.Numerics.Native.Heat158Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat158Y00_formula : nativeHeat158Y00 = nativeHeat158Frames.y := by
  decide +kernel

theorem nativeHeat158All48 : nativeHeatPasses nativeGap159Old nativeHeat158Frames nativeHeat158Coef nativeHeat158Fixed nativeHeat158Base 48 nativeHeat158Frames.y = nativeHeat158Y48 := by
  rw [← nativeHeat158Y00_formula]
  have h4 : nativeHeatPasses nativeGap159Old nativeHeat158Frames nativeHeat158Coef nativeHeat158Fixed nativeHeat158Base 4 nativeHeat158Y00 = nativeHeat158Y04 := nativeHeat158Pass04
  have h8 : nativeHeatPasses nativeGap159Old nativeHeat158Frames nativeHeat158Coef nativeHeat158Fixed nativeHeat158Base 8 nativeHeat158Y00 = nativeHeat158Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat158Pass08]
  have h12 : nativeHeatPasses nativeGap159Old nativeHeat158Frames nativeHeat158Coef nativeHeat158Fixed nativeHeat158Base 12 nativeHeat158Y00 = nativeHeat158Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat158Pass12]
  have h16 : nativeHeatPasses nativeGap159Old nativeHeat158Frames nativeHeat158Coef nativeHeat158Fixed nativeHeat158Base 16 nativeHeat158Y00 = nativeHeat158Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat158Pass16]
  have h20 : nativeHeatPasses nativeGap159Old nativeHeat158Frames nativeHeat158Coef nativeHeat158Fixed nativeHeat158Base 20 nativeHeat158Y00 = nativeHeat158Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat158Pass20]
  have h24 : nativeHeatPasses nativeGap159Old nativeHeat158Frames nativeHeat158Coef nativeHeat158Fixed nativeHeat158Base 24 nativeHeat158Y00 = nativeHeat158Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat158Pass24]
  have h28 : nativeHeatPasses nativeGap159Old nativeHeat158Frames nativeHeat158Coef nativeHeat158Fixed nativeHeat158Base 28 nativeHeat158Y00 = nativeHeat158Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat158Pass28]
  have h32 : nativeHeatPasses nativeGap159Old nativeHeat158Frames nativeHeat158Coef nativeHeat158Fixed nativeHeat158Base 32 nativeHeat158Y00 = nativeHeat158Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat158Pass32]
  have h36 : nativeHeatPasses nativeGap159Old nativeHeat158Frames nativeHeat158Coef nativeHeat158Fixed nativeHeat158Base 36 nativeHeat158Y00 = nativeHeat158Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat158Pass36]
  have h40 : nativeHeatPasses nativeGap159Old nativeHeat158Frames nativeHeat158Coef nativeHeat158Fixed nativeHeat158Base 40 nativeHeat158Y00 = nativeHeat158Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat158Pass40]
  have h44 : nativeHeatPasses nativeGap159Old nativeHeat158Frames nativeHeat158Coef nativeHeat158Fixed nativeHeat158Base 44 nativeHeat158Y00 = nativeHeat158Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat158Pass44]
  have h48 : nativeHeatPasses nativeGap159Old nativeHeat158Frames nativeHeat158Coef nativeHeat158Fixed nativeHeat158Base 48 nativeHeat158Y00 = nativeHeat158Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat158Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
