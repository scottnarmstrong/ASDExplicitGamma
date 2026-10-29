module
public import ASDExplicitGamma.Numerics.Native.Heat119Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat119Y00_formula : nativeHeat119Y00 = nativeHeat119Frames.y := by
  decide +kernel

theorem nativeHeat119All48 : nativeHeatPasses nativeGap120Old nativeHeat119Frames nativeHeat119Coef nativeHeat119Fixed nativeHeat119Base 48 nativeHeat119Frames.y = nativeHeat119Y48 := by
  rw [← nativeHeat119Y00_formula]
  have h4 : nativeHeatPasses nativeGap120Old nativeHeat119Frames nativeHeat119Coef nativeHeat119Fixed nativeHeat119Base 4 nativeHeat119Y00 = nativeHeat119Y04 := nativeHeat119Pass04
  have h8 : nativeHeatPasses nativeGap120Old nativeHeat119Frames nativeHeat119Coef nativeHeat119Fixed nativeHeat119Base 8 nativeHeat119Y00 = nativeHeat119Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat119Pass08]
  have h12 : nativeHeatPasses nativeGap120Old nativeHeat119Frames nativeHeat119Coef nativeHeat119Fixed nativeHeat119Base 12 nativeHeat119Y00 = nativeHeat119Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat119Pass12]
  have h16 : nativeHeatPasses nativeGap120Old nativeHeat119Frames nativeHeat119Coef nativeHeat119Fixed nativeHeat119Base 16 nativeHeat119Y00 = nativeHeat119Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat119Pass16]
  have h20 : nativeHeatPasses nativeGap120Old nativeHeat119Frames nativeHeat119Coef nativeHeat119Fixed nativeHeat119Base 20 nativeHeat119Y00 = nativeHeat119Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat119Pass20]
  have h24 : nativeHeatPasses nativeGap120Old nativeHeat119Frames nativeHeat119Coef nativeHeat119Fixed nativeHeat119Base 24 nativeHeat119Y00 = nativeHeat119Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat119Pass24]
  have h28 : nativeHeatPasses nativeGap120Old nativeHeat119Frames nativeHeat119Coef nativeHeat119Fixed nativeHeat119Base 28 nativeHeat119Y00 = nativeHeat119Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat119Pass28]
  have h32 : nativeHeatPasses nativeGap120Old nativeHeat119Frames nativeHeat119Coef nativeHeat119Fixed nativeHeat119Base 32 nativeHeat119Y00 = nativeHeat119Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat119Pass32]
  have h36 : nativeHeatPasses nativeGap120Old nativeHeat119Frames nativeHeat119Coef nativeHeat119Fixed nativeHeat119Base 36 nativeHeat119Y00 = nativeHeat119Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat119Pass36]
  have h40 : nativeHeatPasses nativeGap120Old nativeHeat119Frames nativeHeat119Coef nativeHeat119Fixed nativeHeat119Base 40 nativeHeat119Y00 = nativeHeat119Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat119Pass40]
  have h44 : nativeHeatPasses nativeGap120Old nativeHeat119Frames nativeHeat119Coef nativeHeat119Fixed nativeHeat119Base 44 nativeHeat119Y00 = nativeHeat119Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat119Pass44]
  have h48 : nativeHeatPasses nativeGap120Old nativeHeat119Frames nativeHeat119Coef nativeHeat119Fixed nativeHeat119Base 48 nativeHeat119Y00 = nativeHeat119Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat119Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
