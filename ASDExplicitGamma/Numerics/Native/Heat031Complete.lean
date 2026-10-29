module
public import ASDExplicitGamma.Numerics.Native.Heat031Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat031Y00_formula : nativeHeat031Y00 = nativeHeat031Frames.y := by
  decide +kernel

theorem nativeHeat031All48 : nativeHeatPasses nativeGap032Old nativeHeat031Frames nativeHeat031Coef nativeHeat031Fixed nativeHeat031Base 48 nativeHeat031Frames.y = nativeHeat031Y48 := by
  rw [← nativeHeat031Y00_formula]
  have h4 : nativeHeatPasses nativeGap032Old nativeHeat031Frames nativeHeat031Coef nativeHeat031Fixed nativeHeat031Base 4 nativeHeat031Y00 = nativeHeat031Y04 := nativeHeat031Pass04
  have h8 : nativeHeatPasses nativeGap032Old nativeHeat031Frames nativeHeat031Coef nativeHeat031Fixed nativeHeat031Base 8 nativeHeat031Y00 = nativeHeat031Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat031Pass08]
  have h12 : nativeHeatPasses nativeGap032Old nativeHeat031Frames nativeHeat031Coef nativeHeat031Fixed nativeHeat031Base 12 nativeHeat031Y00 = nativeHeat031Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat031Pass12]
  have h16 : nativeHeatPasses nativeGap032Old nativeHeat031Frames nativeHeat031Coef nativeHeat031Fixed nativeHeat031Base 16 nativeHeat031Y00 = nativeHeat031Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat031Pass16]
  have h20 : nativeHeatPasses nativeGap032Old nativeHeat031Frames nativeHeat031Coef nativeHeat031Fixed nativeHeat031Base 20 nativeHeat031Y00 = nativeHeat031Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat031Pass20]
  have h24 : nativeHeatPasses nativeGap032Old nativeHeat031Frames nativeHeat031Coef nativeHeat031Fixed nativeHeat031Base 24 nativeHeat031Y00 = nativeHeat031Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat031Pass24]
  have h28 : nativeHeatPasses nativeGap032Old nativeHeat031Frames nativeHeat031Coef nativeHeat031Fixed nativeHeat031Base 28 nativeHeat031Y00 = nativeHeat031Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat031Pass28]
  have h32 : nativeHeatPasses nativeGap032Old nativeHeat031Frames nativeHeat031Coef nativeHeat031Fixed nativeHeat031Base 32 nativeHeat031Y00 = nativeHeat031Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat031Pass32]
  have h36 : nativeHeatPasses nativeGap032Old nativeHeat031Frames nativeHeat031Coef nativeHeat031Fixed nativeHeat031Base 36 nativeHeat031Y00 = nativeHeat031Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat031Pass36]
  have h40 : nativeHeatPasses nativeGap032Old nativeHeat031Frames nativeHeat031Coef nativeHeat031Fixed nativeHeat031Base 40 nativeHeat031Y00 = nativeHeat031Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat031Pass40]
  have h44 : nativeHeatPasses nativeGap032Old nativeHeat031Frames nativeHeat031Coef nativeHeat031Fixed nativeHeat031Base 44 nativeHeat031Y00 = nativeHeat031Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat031Pass44]
  have h48 : nativeHeatPasses nativeGap032Old nativeHeat031Frames nativeHeat031Coef nativeHeat031Fixed nativeHeat031Base 48 nativeHeat031Y00 = nativeHeat031Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat031Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
