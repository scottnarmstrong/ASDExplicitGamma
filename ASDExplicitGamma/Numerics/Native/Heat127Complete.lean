module
public import ASDExplicitGamma.Numerics.Native.Heat127Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat127Y00_formula : nativeHeat127Y00 = nativeHeat127Frames.y := by
  decide +kernel

theorem nativeHeat127All48 : nativeHeatPasses nativeGap128Old nativeHeat127Frames nativeHeat127Coef nativeHeat127Fixed nativeHeat127Base 48 nativeHeat127Frames.y = nativeHeat127Y48 := by
  rw [← nativeHeat127Y00_formula]
  have h4 : nativeHeatPasses nativeGap128Old nativeHeat127Frames nativeHeat127Coef nativeHeat127Fixed nativeHeat127Base 4 nativeHeat127Y00 = nativeHeat127Y04 := nativeHeat127Pass04
  have h8 : nativeHeatPasses nativeGap128Old nativeHeat127Frames nativeHeat127Coef nativeHeat127Fixed nativeHeat127Base 8 nativeHeat127Y00 = nativeHeat127Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat127Pass08]
  have h12 : nativeHeatPasses nativeGap128Old nativeHeat127Frames nativeHeat127Coef nativeHeat127Fixed nativeHeat127Base 12 nativeHeat127Y00 = nativeHeat127Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat127Pass12]
  have h16 : nativeHeatPasses nativeGap128Old nativeHeat127Frames nativeHeat127Coef nativeHeat127Fixed nativeHeat127Base 16 nativeHeat127Y00 = nativeHeat127Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat127Pass16]
  have h20 : nativeHeatPasses nativeGap128Old nativeHeat127Frames nativeHeat127Coef nativeHeat127Fixed nativeHeat127Base 20 nativeHeat127Y00 = nativeHeat127Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat127Pass20]
  have h24 : nativeHeatPasses nativeGap128Old nativeHeat127Frames nativeHeat127Coef nativeHeat127Fixed nativeHeat127Base 24 nativeHeat127Y00 = nativeHeat127Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat127Pass24]
  have h28 : nativeHeatPasses nativeGap128Old nativeHeat127Frames nativeHeat127Coef nativeHeat127Fixed nativeHeat127Base 28 nativeHeat127Y00 = nativeHeat127Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat127Pass28]
  have h32 : nativeHeatPasses nativeGap128Old nativeHeat127Frames nativeHeat127Coef nativeHeat127Fixed nativeHeat127Base 32 nativeHeat127Y00 = nativeHeat127Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat127Pass32]
  have h36 : nativeHeatPasses nativeGap128Old nativeHeat127Frames nativeHeat127Coef nativeHeat127Fixed nativeHeat127Base 36 nativeHeat127Y00 = nativeHeat127Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat127Pass36]
  have h40 : nativeHeatPasses nativeGap128Old nativeHeat127Frames nativeHeat127Coef nativeHeat127Fixed nativeHeat127Base 40 nativeHeat127Y00 = nativeHeat127Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat127Pass40]
  have h44 : nativeHeatPasses nativeGap128Old nativeHeat127Frames nativeHeat127Coef nativeHeat127Fixed nativeHeat127Base 44 nativeHeat127Y00 = nativeHeat127Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat127Pass44]
  have h48 : nativeHeatPasses nativeGap128Old nativeHeat127Frames nativeHeat127Coef nativeHeat127Fixed nativeHeat127Base 48 nativeHeat127Y00 = nativeHeat127Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat127Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
