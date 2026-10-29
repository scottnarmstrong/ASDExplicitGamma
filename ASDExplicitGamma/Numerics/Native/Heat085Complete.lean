module
public import ASDExplicitGamma.Numerics.Native.Heat085Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat085Y00_formula : nativeHeat085Y00 = nativeHeat085Frames.y := by
  decide +kernel

theorem nativeHeat085All48 : nativeHeatPasses nativeGap086Old nativeHeat085Frames nativeHeat085Coef nativeHeat085Fixed nativeHeat085Base 48 nativeHeat085Frames.y = nativeHeat085Y48 := by
  rw [← nativeHeat085Y00_formula]
  have h4 : nativeHeatPasses nativeGap086Old nativeHeat085Frames nativeHeat085Coef nativeHeat085Fixed nativeHeat085Base 4 nativeHeat085Y00 = nativeHeat085Y04 := nativeHeat085Pass04
  have h8 : nativeHeatPasses nativeGap086Old nativeHeat085Frames nativeHeat085Coef nativeHeat085Fixed nativeHeat085Base 8 nativeHeat085Y00 = nativeHeat085Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat085Pass08]
  have h12 : nativeHeatPasses nativeGap086Old nativeHeat085Frames nativeHeat085Coef nativeHeat085Fixed nativeHeat085Base 12 nativeHeat085Y00 = nativeHeat085Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat085Pass12]
  have h16 : nativeHeatPasses nativeGap086Old nativeHeat085Frames nativeHeat085Coef nativeHeat085Fixed nativeHeat085Base 16 nativeHeat085Y00 = nativeHeat085Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat085Pass16]
  have h20 : nativeHeatPasses nativeGap086Old nativeHeat085Frames nativeHeat085Coef nativeHeat085Fixed nativeHeat085Base 20 nativeHeat085Y00 = nativeHeat085Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat085Pass20]
  have h24 : nativeHeatPasses nativeGap086Old nativeHeat085Frames nativeHeat085Coef nativeHeat085Fixed nativeHeat085Base 24 nativeHeat085Y00 = nativeHeat085Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat085Pass24]
  have h28 : nativeHeatPasses nativeGap086Old nativeHeat085Frames nativeHeat085Coef nativeHeat085Fixed nativeHeat085Base 28 nativeHeat085Y00 = nativeHeat085Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat085Pass28]
  have h32 : nativeHeatPasses nativeGap086Old nativeHeat085Frames nativeHeat085Coef nativeHeat085Fixed nativeHeat085Base 32 nativeHeat085Y00 = nativeHeat085Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat085Pass32]
  have h36 : nativeHeatPasses nativeGap086Old nativeHeat085Frames nativeHeat085Coef nativeHeat085Fixed nativeHeat085Base 36 nativeHeat085Y00 = nativeHeat085Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat085Pass36]
  have h40 : nativeHeatPasses nativeGap086Old nativeHeat085Frames nativeHeat085Coef nativeHeat085Fixed nativeHeat085Base 40 nativeHeat085Y00 = nativeHeat085Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat085Pass40]
  have h44 : nativeHeatPasses nativeGap086Old nativeHeat085Frames nativeHeat085Coef nativeHeat085Fixed nativeHeat085Base 44 nativeHeat085Y00 = nativeHeat085Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat085Pass44]
  have h48 : nativeHeatPasses nativeGap086Old nativeHeat085Frames nativeHeat085Coef nativeHeat085Fixed nativeHeat085Base 48 nativeHeat085Y00 = nativeHeat085Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat085Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
