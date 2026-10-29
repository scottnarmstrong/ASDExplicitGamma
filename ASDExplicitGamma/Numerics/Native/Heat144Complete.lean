module
public import ASDExplicitGamma.Numerics.Native.Heat144Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat144Y00_formula : nativeHeat144Y00 = nativeHeat144Frames.y := by
  decide +kernel

theorem nativeHeat144All48 : nativeHeatPasses nativeGap145Old nativeHeat144Frames nativeHeat144Coef nativeHeat144Fixed nativeHeat144Base 48 nativeHeat144Frames.y = nativeHeat144Y48 := by
  rw [← nativeHeat144Y00_formula]
  have h4 : nativeHeatPasses nativeGap145Old nativeHeat144Frames nativeHeat144Coef nativeHeat144Fixed nativeHeat144Base 4 nativeHeat144Y00 = nativeHeat144Y04 := nativeHeat144Pass04
  have h8 : nativeHeatPasses nativeGap145Old nativeHeat144Frames nativeHeat144Coef nativeHeat144Fixed nativeHeat144Base 8 nativeHeat144Y00 = nativeHeat144Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat144Pass08]
  have h12 : nativeHeatPasses nativeGap145Old nativeHeat144Frames nativeHeat144Coef nativeHeat144Fixed nativeHeat144Base 12 nativeHeat144Y00 = nativeHeat144Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat144Pass12]
  have h16 : nativeHeatPasses nativeGap145Old nativeHeat144Frames nativeHeat144Coef nativeHeat144Fixed nativeHeat144Base 16 nativeHeat144Y00 = nativeHeat144Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat144Pass16]
  have h20 : nativeHeatPasses nativeGap145Old nativeHeat144Frames nativeHeat144Coef nativeHeat144Fixed nativeHeat144Base 20 nativeHeat144Y00 = nativeHeat144Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat144Pass20]
  have h24 : nativeHeatPasses nativeGap145Old nativeHeat144Frames nativeHeat144Coef nativeHeat144Fixed nativeHeat144Base 24 nativeHeat144Y00 = nativeHeat144Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat144Pass24]
  have h28 : nativeHeatPasses nativeGap145Old nativeHeat144Frames nativeHeat144Coef nativeHeat144Fixed nativeHeat144Base 28 nativeHeat144Y00 = nativeHeat144Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat144Pass28]
  have h32 : nativeHeatPasses nativeGap145Old nativeHeat144Frames nativeHeat144Coef nativeHeat144Fixed nativeHeat144Base 32 nativeHeat144Y00 = nativeHeat144Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat144Pass32]
  have h36 : nativeHeatPasses nativeGap145Old nativeHeat144Frames nativeHeat144Coef nativeHeat144Fixed nativeHeat144Base 36 nativeHeat144Y00 = nativeHeat144Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat144Pass36]
  have h40 : nativeHeatPasses nativeGap145Old nativeHeat144Frames nativeHeat144Coef nativeHeat144Fixed nativeHeat144Base 40 nativeHeat144Y00 = nativeHeat144Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat144Pass40]
  have h44 : nativeHeatPasses nativeGap145Old nativeHeat144Frames nativeHeat144Coef nativeHeat144Fixed nativeHeat144Base 44 nativeHeat144Y00 = nativeHeat144Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat144Pass44]
  have h48 : nativeHeatPasses nativeGap145Old nativeHeat144Frames nativeHeat144Coef nativeHeat144Fixed nativeHeat144Base 48 nativeHeat144Y00 = nativeHeat144Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat144Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
