module
public import ASDExplicitGamma.Numerics.Native.Heat115Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat115Y00_formula : nativeHeat115Y00 = nativeHeat115Frames.y := by
  decide +kernel

theorem nativeHeat115All48 : nativeHeatPasses nativeGap116Old nativeHeat115Frames nativeHeat115Coef nativeHeat115Fixed nativeHeat115Base 48 nativeHeat115Frames.y = nativeHeat115Y48 := by
  rw [← nativeHeat115Y00_formula]
  have h4 : nativeHeatPasses nativeGap116Old nativeHeat115Frames nativeHeat115Coef nativeHeat115Fixed nativeHeat115Base 4 nativeHeat115Y00 = nativeHeat115Y04 := nativeHeat115Pass04
  have h8 : nativeHeatPasses nativeGap116Old nativeHeat115Frames nativeHeat115Coef nativeHeat115Fixed nativeHeat115Base 8 nativeHeat115Y00 = nativeHeat115Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat115Pass08]
  have h12 : nativeHeatPasses nativeGap116Old nativeHeat115Frames nativeHeat115Coef nativeHeat115Fixed nativeHeat115Base 12 nativeHeat115Y00 = nativeHeat115Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat115Pass12]
  have h16 : nativeHeatPasses nativeGap116Old nativeHeat115Frames nativeHeat115Coef nativeHeat115Fixed nativeHeat115Base 16 nativeHeat115Y00 = nativeHeat115Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat115Pass16]
  have h20 : nativeHeatPasses nativeGap116Old nativeHeat115Frames nativeHeat115Coef nativeHeat115Fixed nativeHeat115Base 20 nativeHeat115Y00 = nativeHeat115Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat115Pass20]
  have h24 : nativeHeatPasses nativeGap116Old nativeHeat115Frames nativeHeat115Coef nativeHeat115Fixed nativeHeat115Base 24 nativeHeat115Y00 = nativeHeat115Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat115Pass24]
  have h28 : nativeHeatPasses nativeGap116Old nativeHeat115Frames nativeHeat115Coef nativeHeat115Fixed nativeHeat115Base 28 nativeHeat115Y00 = nativeHeat115Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat115Pass28]
  have h32 : nativeHeatPasses nativeGap116Old nativeHeat115Frames nativeHeat115Coef nativeHeat115Fixed nativeHeat115Base 32 nativeHeat115Y00 = nativeHeat115Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat115Pass32]
  have h36 : nativeHeatPasses nativeGap116Old nativeHeat115Frames nativeHeat115Coef nativeHeat115Fixed nativeHeat115Base 36 nativeHeat115Y00 = nativeHeat115Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat115Pass36]
  have h40 : nativeHeatPasses nativeGap116Old nativeHeat115Frames nativeHeat115Coef nativeHeat115Fixed nativeHeat115Base 40 nativeHeat115Y00 = nativeHeat115Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat115Pass40]
  have h44 : nativeHeatPasses nativeGap116Old nativeHeat115Frames nativeHeat115Coef nativeHeat115Fixed nativeHeat115Base 44 nativeHeat115Y00 = nativeHeat115Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat115Pass44]
  have h48 : nativeHeatPasses nativeGap116Old nativeHeat115Frames nativeHeat115Coef nativeHeat115Fixed nativeHeat115Base 48 nativeHeat115Y00 = nativeHeat115Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat115Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
