module
public import ASDExplicitGamma.Numerics.Native.Heat129Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat129Y00_formula : nativeHeat129Y00 = nativeHeat129Frames.y := by
  decide +kernel

theorem nativeHeat129All48 : nativeHeatPasses nativeGap130Old nativeHeat129Frames nativeHeat129Coef nativeHeat129Fixed nativeHeat129Base 48 nativeHeat129Frames.y = nativeHeat129Y48 := by
  rw [← nativeHeat129Y00_formula]
  have h4 : nativeHeatPasses nativeGap130Old nativeHeat129Frames nativeHeat129Coef nativeHeat129Fixed nativeHeat129Base 4 nativeHeat129Y00 = nativeHeat129Y04 := nativeHeat129Pass04
  have h8 : nativeHeatPasses nativeGap130Old nativeHeat129Frames nativeHeat129Coef nativeHeat129Fixed nativeHeat129Base 8 nativeHeat129Y00 = nativeHeat129Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat129Pass08]
  have h12 : nativeHeatPasses nativeGap130Old nativeHeat129Frames nativeHeat129Coef nativeHeat129Fixed nativeHeat129Base 12 nativeHeat129Y00 = nativeHeat129Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat129Pass12]
  have h16 : nativeHeatPasses nativeGap130Old nativeHeat129Frames nativeHeat129Coef nativeHeat129Fixed nativeHeat129Base 16 nativeHeat129Y00 = nativeHeat129Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat129Pass16]
  have h20 : nativeHeatPasses nativeGap130Old nativeHeat129Frames nativeHeat129Coef nativeHeat129Fixed nativeHeat129Base 20 nativeHeat129Y00 = nativeHeat129Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat129Pass20]
  have h24 : nativeHeatPasses nativeGap130Old nativeHeat129Frames nativeHeat129Coef nativeHeat129Fixed nativeHeat129Base 24 nativeHeat129Y00 = nativeHeat129Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat129Pass24]
  have h28 : nativeHeatPasses nativeGap130Old nativeHeat129Frames nativeHeat129Coef nativeHeat129Fixed nativeHeat129Base 28 nativeHeat129Y00 = nativeHeat129Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat129Pass28]
  have h32 : nativeHeatPasses nativeGap130Old nativeHeat129Frames nativeHeat129Coef nativeHeat129Fixed nativeHeat129Base 32 nativeHeat129Y00 = nativeHeat129Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat129Pass32]
  have h36 : nativeHeatPasses nativeGap130Old nativeHeat129Frames nativeHeat129Coef nativeHeat129Fixed nativeHeat129Base 36 nativeHeat129Y00 = nativeHeat129Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat129Pass36]
  have h40 : nativeHeatPasses nativeGap130Old nativeHeat129Frames nativeHeat129Coef nativeHeat129Fixed nativeHeat129Base 40 nativeHeat129Y00 = nativeHeat129Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat129Pass40]
  have h44 : nativeHeatPasses nativeGap130Old nativeHeat129Frames nativeHeat129Coef nativeHeat129Fixed nativeHeat129Base 44 nativeHeat129Y00 = nativeHeat129Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat129Pass44]
  have h48 : nativeHeatPasses nativeGap130Old nativeHeat129Frames nativeHeat129Coef nativeHeat129Fixed nativeHeat129Base 48 nativeHeat129Y00 = nativeHeat129Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat129Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
