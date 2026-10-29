module
public import ASDExplicitGamma.Numerics.Native.Heat102Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat102Y00_formula : nativeHeat102Y00 = nativeHeat102Frames.y := by
  decide +kernel

theorem nativeHeat102All48 : nativeHeatPasses nativeGap103Old nativeHeat102Frames nativeHeat102Coef nativeHeat102Fixed nativeHeat102Base 48 nativeHeat102Frames.y = nativeHeat102Y48 := by
  rw [← nativeHeat102Y00_formula]
  have h4 : nativeHeatPasses nativeGap103Old nativeHeat102Frames nativeHeat102Coef nativeHeat102Fixed nativeHeat102Base 4 nativeHeat102Y00 = nativeHeat102Y04 := nativeHeat102Pass04
  have h8 : nativeHeatPasses nativeGap103Old nativeHeat102Frames nativeHeat102Coef nativeHeat102Fixed nativeHeat102Base 8 nativeHeat102Y00 = nativeHeat102Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat102Pass08]
  have h12 : nativeHeatPasses nativeGap103Old nativeHeat102Frames nativeHeat102Coef nativeHeat102Fixed nativeHeat102Base 12 nativeHeat102Y00 = nativeHeat102Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat102Pass12]
  have h16 : nativeHeatPasses nativeGap103Old nativeHeat102Frames nativeHeat102Coef nativeHeat102Fixed nativeHeat102Base 16 nativeHeat102Y00 = nativeHeat102Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat102Pass16]
  have h20 : nativeHeatPasses nativeGap103Old nativeHeat102Frames nativeHeat102Coef nativeHeat102Fixed nativeHeat102Base 20 nativeHeat102Y00 = nativeHeat102Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat102Pass20]
  have h24 : nativeHeatPasses nativeGap103Old nativeHeat102Frames nativeHeat102Coef nativeHeat102Fixed nativeHeat102Base 24 nativeHeat102Y00 = nativeHeat102Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat102Pass24]
  have h28 : nativeHeatPasses nativeGap103Old nativeHeat102Frames nativeHeat102Coef nativeHeat102Fixed nativeHeat102Base 28 nativeHeat102Y00 = nativeHeat102Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat102Pass28]
  have h32 : nativeHeatPasses nativeGap103Old nativeHeat102Frames nativeHeat102Coef nativeHeat102Fixed nativeHeat102Base 32 nativeHeat102Y00 = nativeHeat102Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat102Pass32]
  have h36 : nativeHeatPasses nativeGap103Old nativeHeat102Frames nativeHeat102Coef nativeHeat102Fixed nativeHeat102Base 36 nativeHeat102Y00 = nativeHeat102Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat102Pass36]
  have h40 : nativeHeatPasses nativeGap103Old nativeHeat102Frames nativeHeat102Coef nativeHeat102Fixed nativeHeat102Base 40 nativeHeat102Y00 = nativeHeat102Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat102Pass40]
  have h44 : nativeHeatPasses nativeGap103Old nativeHeat102Frames nativeHeat102Coef nativeHeat102Fixed nativeHeat102Base 44 nativeHeat102Y00 = nativeHeat102Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat102Pass44]
  have h48 : nativeHeatPasses nativeGap103Old nativeHeat102Frames nativeHeat102Coef nativeHeat102Fixed nativeHeat102Base 48 nativeHeat102Y00 = nativeHeat102Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat102Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
