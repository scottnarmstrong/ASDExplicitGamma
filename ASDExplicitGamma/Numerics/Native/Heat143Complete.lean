module
public import ASDExplicitGamma.Numerics.Native.Heat143Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat143Y00_formula : nativeHeat143Y00 = nativeHeat143Frames.y := by
  decide +kernel

theorem nativeHeat143All48 : nativeHeatPasses nativeGap144Old nativeHeat143Frames nativeHeat143Coef nativeHeat143Fixed nativeHeat143Base 48 nativeHeat143Frames.y = nativeHeat143Y48 := by
  rw [← nativeHeat143Y00_formula]
  have h4 : nativeHeatPasses nativeGap144Old nativeHeat143Frames nativeHeat143Coef nativeHeat143Fixed nativeHeat143Base 4 nativeHeat143Y00 = nativeHeat143Y04 := nativeHeat143Pass04
  have h8 : nativeHeatPasses nativeGap144Old nativeHeat143Frames nativeHeat143Coef nativeHeat143Fixed nativeHeat143Base 8 nativeHeat143Y00 = nativeHeat143Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat143Pass08]
  have h12 : nativeHeatPasses nativeGap144Old nativeHeat143Frames nativeHeat143Coef nativeHeat143Fixed nativeHeat143Base 12 nativeHeat143Y00 = nativeHeat143Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat143Pass12]
  have h16 : nativeHeatPasses nativeGap144Old nativeHeat143Frames nativeHeat143Coef nativeHeat143Fixed nativeHeat143Base 16 nativeHeat143Y00 = nativeHeat143Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat143Pass16]
  have h20 : nativeHeatPasses nativeGap144Old nativeHeat143Frames nativeHeat143Coef nativeHeat143Fixed nativeHeat143Base 20 nativeHeat143Y00 = nativeHeat143Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat143Pass20]
  have h24 : nativeHeatPasses nativeGap144Old nativeHeat143Frames nativeHeat143Coef nativeHeat143Fixed nativeHeat143Base 24 nativeHeat143Y00 = nativeHeat143Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat143Pass24]
  have h28 : nativeHeatPasses nativeGap144Old nativeHeat143Frames nativeHeat143Coef nativeHeat143Fixed nativeHeat143Base 28 nativeHeat143Y00 = nativeHeat143Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat143Pass28]
  have h32 : nativeHeatPasses nativeGap144Old nativeHeat143Frames nativeHeat143Coef nativeHeat143Fixed nativeHeat143Base 32 nativeHeat143Y00 = nativeHeat143Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat143Pass32]
  have h36 : nativeHeatPasses nativeGap144Old nativeHeat143Frames nativeHeat143Coef nativeHeat143Fixed nativeHeat143Base 36 nativeHeat143Y00 = nativeHeat143Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat143Pass36]
  have h40 : nativeHeatPasses nativeGap144Old nativeHeat143Frames nativeHeat143Coef nativeHeat143Fixed nativeHeat143Base 40 nativeHeat143Y00 = nativeHeat143Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat143Pass40]
  have h44 : nativeHeatPasses nativeGap144Old nativeHeat143Frames nativeHeat143Coef nativeHeat143Fixed nativeHeat143Base 44 nativeHeat143Y00 = nativeHeat143Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat143Pass44]
  have h48 : nativeHeatPasses nativeGap144Old nativeHeat143Frames nativeHeat143Coef nativeHeat143Fixed nativeHeat143Base 48 nativeHeat143Y00 = nativeHeat143Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat143Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
