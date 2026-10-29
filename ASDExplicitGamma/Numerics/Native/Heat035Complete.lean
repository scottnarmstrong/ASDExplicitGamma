module
public import ASDExplicitGamma.Numerics.Native.Heat035Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat035Y00_formula : nativeHeat035Y00 = nativeHeat035Frames.y := by
  decide +kernel

theorem nativeHeat035All48 : nativeHeatPasses nativeGap036Old nativeHeat035Frames nativeHeat035Coef nativeHeat035Fixed nativeHeat035Base 48 nativeHeat035Frames.y = nativeHeat035Y48 := by
  rw [← nativeHeat035Y00_formula]
  have h4 : nativeHeatPasses nativeGap036Old nativeHeat035Frames nativeHeat035Coef nativeHeat035Fixed nativeHeat035Base 4 nativeHeat035Y00 = nativeHeat035Y04 := nativeHeat035Pass04
  have h8 : nativeHeatPasses nativeGap036Old nativeHeat035Frames nativeHeat035Coef nativeHeat035Fixed nativeHeat035Base 8 nativeHeat035Y00 = nativeHeat035Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat035Pass08]
  have h12 : nativeHeatPasses nativeGap036Old nativeHeat035Frames nativeHeat035Coef nativeHeat035Fixed nativeHeat035Base 12 nativeHeat035Y00 = nativeHeat035Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat035Pass12]
  have h16 : nativeHeatPasses nativeGap036Old nativeHeat035Frames nativeHeat035Coef nativeHeat035Fixed nativeHeat035Base 16 nativeHeat035Y00 = nativeHeat035Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat035Pass16]
  have h20 : nativeHeatPasses nativeGap036Old nativeHeat035Frames nativeHeat035Coef nativeHeat035Fixed nativeHeat035Base 20 nativeHeat035Y00 = nativeHeat035Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat035Pass20]
  have h24 : nativeHeatPasses nativeGap036Old nativeHeat035Frames nativeHeat035Coef nativeHeat035Fixed nativeHeat035Base 24 nativeHeat035Y00 = nativeHeat035Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat035Pass24]
  have h28 : nativeHeatPasses nativeGap036Old nativeHeat035Frames nativeHeat035Coef nativeHeat035Fixed nativeHeat035Base 28 nativeHeat035Y00 = nativeHeat035Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat035Pass28]
  have h32 : nativeHeatPasses nativeGap036Old nativeHeat035Frames nativeHeat035Coef nativeHeat035Fixed nativeHeat035Base 32 nativeHeat035Y00 = nativeHeat035Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat035Pass32]
  have h36 : nativeHeatPasses nativeGap036Old nativeHeat035Frames nativeHeat035Coef nativeHeat035Fixed nativeHeat035Base 36 nativeHeat035Y00 = nativeHeat035Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat035Pass36]
  have h40 : nativeHeatPasses nativeGap036Old nativeHeat035Frames nativeHeat035Coef nativeHeat035Fixed nativeHeat035Base 40 nativeHeat035Y00 = nativeHeat035Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat035Pass40]
  have h44 : nativeHeatPasses nativeGap036Old nativeHeat035Frames nativeHeat035Coef nativeHeat035Fixed nativeHeat035Base 44 nativeHeat035Y00 = nativeHeat035Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat035Pass44]
  have h48 : nativeHeatPasses nativeGap036Old nativeHeat035Frames nativeHeat035Coef nativeHeat035Fixed nativeHeat035Base 48 nativeHeat035Y00 = nativeHeat035Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat035Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
