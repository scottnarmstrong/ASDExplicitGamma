module
public import ASDExplicitGamma.Numerics.Native.Heat020Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat020Y00_formula : nativeHeat020Y00 = nativeHeat020Frames.y := by
  decide +kernel

theorem nativeHeat020All48 : nativeHeatPasses nativeGap021Old nativeHeat020Frames nativeHeat020Coef nativeHeat020Fixed nativeHeat020Base 48 nativeHeat020Frames.y = nativeHeat020Y48 := by
  rw [← nativeHeat020Y00_formula]
  have h4 : nativeHeatPasses nativeGap021Old nativeHeat020Frames nativeHeat020Coef nativeHeat020Fixed nativeHeat020Base 4 nativeHeat020Y00 = nativeHeat020Y04 := nativeHeat020Pass04
  have h8 : nativeHeatPasses nativeGap021Old nativeHeat020Frames nativeHeat020Coef nativeHeat020Fixed nativeHeat020Base 8 nativeHeat020Y00 = nativeHeat020Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat020Pass08]
  have h12 : nativeHeatPasses nativeGap021Old nativeHeat020Frames nativeHeat020Coef nativeHeat020Fixed nativeHeat020Base 12 nativeHeat020Y00 = nativeHeat020Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat020Pass12]
  have h16 : nativeHeatPasses nativeGap021Old nativeHeat020Frames nativeHeat020Coef nativeHeat020Fixed nativeHeat020Base 16 nativeHeat020Y00 = nativeHeat020Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat020Pass16]
  have h20 : nativeHeatPasses nativeGap021Old nativeHeat020Frames nativeHeat020Coef nativeHeat020Fixed nativeHeat020Base 20 nativeHeat020Y00 = nativeHeat020Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat020Pass20]
  have h24 : nativeHeatPasses nativeGap021Old nativeHeat020Frames nativeHeat020Coef nativeHeat020Fixed nativeHeat020Base 24 nativeHeat020Y00 = nativeHeat020Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat020Pass24]
  have h28 : nativeHeatPasses nativeGap021Old nativeHeat020Frames nativeHeat020Coef nativeHeat020Fixed nativeHeat020Base 28 nativeHeat020Y00 = nativeHeat020Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat020Pass28]
  have h32 : nativeHeatPasses nativeGap021Old nativeHeat020Frames nativeHeat020Coef nativeHeat020Fixed nativeHeat020Base 32 nativeHeat020Y00 = nativeHeat020Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat020Pass32]
  have h36 : nativeHeatPasses nativeGap021Old nativeHeat020Frames nativeHeat020Coef nativeHeat020Fixed nativeHeat020Base 36 nativeHeat020Y00 = nativeHeat020Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat020Pass36]
  have h40 : nativeHeatPasses nativeGap021Old nativeHeat020Frames nativeHeat020Coef nativeHeat020Fixed nativeHeat020Base 40 nativeHeat020Y00 = nativeHeat020Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat020Pass40]
  have h44 : nativeHeatPasses nativeGap021Old nativeHeat020Frames nativeHeat020Coef nativeHeat020Fixed nativeHeat020Base 44 nativeHeat020Y00 = nativeHeat020Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat020Pass44]
  have h48 : nativeHeatPasses nativeGap021Old nativeHeat020Frames nativeHeat020Coef nativeHeat020Fixed nativeHeat020Base 48 nativeHeat020Y00 = nativeHeat020Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat020Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
