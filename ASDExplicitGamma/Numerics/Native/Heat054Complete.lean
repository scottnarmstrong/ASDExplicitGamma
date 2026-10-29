module
public import ASDExplicitGamma.Numerics.Native.Heat054Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat054Y00_formula : nativeHeat054Y00 = nativeHeat054Frames.y := by
  decide +kernel

theorem nativeHeat054All48 : nativeHeatPasses nativeGap055Old nativeHeat054Frames nativeHeat054Coef nativeHeat054Fixed nativeHeat054Base 48 nativeHeat054Frames.y = nativeHeat054Y48 := by
  rw [← nativeHeat054Y00_formula]
  have h4 : nativeHeatPasses nativeGap055Old nativeHeat054Frames nativeHeat054Coef nativeHeat054Fixed nativeHeat054Base 4 nativeHeat054Y00 = nativeHeat054Y04 := nativeHeat054Pass04
  have h8 : nativeHeatPasses nativeGap055Old nativeHeat054Frames nativeHeat054Coef nativeHeat054Fixed nativeHeat054Base 8 nativeHeat054Y00 = nativeHeat054Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat054Pass08]
  have h12 : nativeHeatPasses nativeGap055Old nativeHeat054Frames nativeHeat054Coef nativeHeat054Fixed nativeHeat054Base 12 nativeHeat054Y00 = nativeHeat054Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat054Pass12]
  have h16 : nativeHeatPasses nativeGap055Old nativeHeat054Frames nativeHeat054Coef nativeHeat054Fixed nativeHeat054Base 16 nativeHeat054Y00 = nativeHeat054Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat054Pass16]
  have h20 : nativeHeatPasses nativeGap055Old nativeHeat054Frames nativeHeat054Coef nativeHeat054Fixed nativeHeat054Base 20 nativeHeat054Y00 = nativeHeat054Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat054Pass20]
  have h24 : nativeHeatPasses nativeGap055Old nativeHeat054Frames nativeHeat054Coef nativeHeat054Fixed nativeHeat054Base 24 nativeHeat054Y00 = nativeHeat054Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat054Pass24]
  have h28 : nativeHeatPasses nativeGap055Old nativeHeat054Frames nativeHeat054Coef nativeHeat054Fixed nativeHeat054Base 28 nativeHeat054Y00 = nativeHeat054Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat054Pass28]
  have h32 : nativeHeatPasses nativeGap055Old nativeHeat054Frames nativeHeat054Coef nativeHeat054Fixed nativeHeat054Base 32 nativeHeat054Y00 = nativeHeat054Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat054Pass32]
  have h36 : nativeHeatPasses nativeGap055Old nativeHeat054Frames nativeHeat054Coef nativeHeat054Fixed nativeHeat054Base 36 nativeHeat054Y00 = nativeHeat054Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat054Pass36]
  have h40 : nativeHeatPasses nativeGap055Old nativeHeat054Frames nativeHeat054Coef nativeHeat054Fixed nativeHeat054Base 40 nativeHeat054Y00 = nativeHeat054Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat054Pass40]
  have h44 : nativeHeatPasses nativeGap055Old nativeHeat054Frames nativeHeat054Coef nativeHeat054Fixed nativeHeat054Base 44 nativeHeat054Y00 = nativeHeat054Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat054Pass44]
  have h48 : nativeHeatPasses nativeGap055Old nativeHeat054Frames nativeHeat054Coef nativeHeat054Fixed nativeHeat054Base 48 nativeHeat054Y00 = nativeHeat054Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat054Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
