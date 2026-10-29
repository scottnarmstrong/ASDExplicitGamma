module
public import ASDExplicitGamma.Numerics.Native.Heat126Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat126Y00_formula : nativeHeat126Y00 = nativeHeat126Frames.y := by
  decide +kernel

theorem nativeHeat126All48 : nativeHeatPasses nativeGap127Old nativeHeat126Frames nativeHeat126Coef nativeHeat126Fixed nativeHeat126Base 48 nativeHeat126Frames.y = nativeHeat126Y48 := by
  rw [← nativeHeat126Y00_formula]
  have h4 : nativeHeatPasses nativeGap127Old nativeHeat126Frames nativeHeat126Coef nativeHeat126Fixed nativeHeat126Base 4 nativeHeat126Y00 = nativeHeat126Y04 := nativeHeat126Pass04
  have h8 : nativeHeatPasses nativeGap127Old nativeHeat126Frames nativeHeat126Coef nativeHeat126Fixed nativeHeat126Base 8 nativeHeat126Y00 = nativeHeat126Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat126Pass08]
  have h12 : nativeHeatPasses nativeGap127Old nativeHeat126Frames nativeHeat126Coef nativeHeat126Fixed nativeHeat126Base 12 nativeHeat126Y00 = nativeHeat126Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat126Pass12]
  have h16 : nativeHeatPasses nativeGap127Old nativeHeat126Frames nativeHeat126Coef nativeHeat126Fixed nativeHeat126Base 16 nativeHeat126Y00 = nativeHeat126Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat126Pass16]
  have h20 : nativeHeatPasses nativeGap127Old nativeHeat126Frames nativeHeat126Coef nativeHeat126Fixed nativeHeat126Base 20 nativeHeat126Y00 = nativeHeat126Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat126Pass20]
  have h24 : nativeHeatPasses nativeGap127Old nativeHeat126Frames nativeHeat126Coef nativeHeat126Fixed nativeHeat126Base 24 nativeHeat126Y00 = nativeHeat126Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat126Pass24]
  have h28 : nativeHeatPasses nativeGap127Old nativeHeat126Frames nativeHeat126Coef nativeHeat126Fixed nativeHeat126Base 28 nativeHeat126Y00 = nativeHeat126Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat126Pass28]
  have h32 : nativeHeatPasses nativeGap127Old nativeHeat126Frames nativeHeat126Coef nativeHeat126Fixed nativeHeat126Base 32 nativeHeat126Y00 = nativeHeat126Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat126Pass32]
  have h36 : nativeHeatPasses nativeGap127Old nativeHeat126Frames nativeHeat126Coef nativeHeat126Fixed nativeHeat126Base 36 nativeHeat126Y00 = nativeHeat126Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat126Pass36]
  have h40 : nativeHeatPasses nativeGap127Old nativeHeat126Frames nativeHeat126Coef nativeHeat126Fixed nativeHeat126Base 40 nativeHeat126Y00 = nativeHeat126Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat126Pass40]
  have h44 : nativeHeatPasses nativeGap127Old nativeHeat126Frames nativeHeat126Coef nativeHeat126Fixed nativeHeat126Base 44 nativeHeat126Y00 = nativeHeat126Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat126Pass44]
  have h48 : nativeHeatPasses nativeGap127Old nativeHeat126Frames nativeHeat126Coef nativeHeat126Fixed nativeHeat126Base 48 nativeHeat126Y00 = nativeHeat126Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat126Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
