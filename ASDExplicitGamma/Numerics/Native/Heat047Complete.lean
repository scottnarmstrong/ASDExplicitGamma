module
public import ASDExplicitGamma.Numerics.Native.Heat047Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat047Y00_formula : nativeHeat047Y00 = nativeHeat047Frames.y := by
  decide +kernel

theorem nativeHeat047All48 : nativeHeatPasses nativeGap048Old nativeHeat047Frames nativeHeat047Coef nativeHeat047Fixed nativeHeat047Base 48 nativeHeat047Frames.y = nativeHeat047Y48 := by
  rw [← nativeHeat047Y00_formula]
  have h4 : nativeHeatPasses nativeGap048Old nativeHeat047Frames nativeHeat047Coef nativeHeat047Fixed nativeHeat047Base 4 nativeHeat047Y00 = nativeHeat047Y04 := nativeHeat047Pass04
  have h8 : nativeHeatPasses nativeGap048Old nativeHeat047Frames nativeHeat047Coef nativeHeat047Fixed nativeHeat047Base 8 nativeHeat047Y00 = nativeHeat047Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat047Pass08]
  have h12 : nativeHeatPasses nativeGap048Old nativeHeat047Frames nativeHeat047Coef nativeHeat047Fixed nativeHeat047Base 12 nativeHeat047Y00 = nativeHeat047Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat047Pass12]
  have h16 : nativeHeatPasses nativeGap048Old nativeHeat047Frames nativeHeat047Coef nativeHeat047Fixed nativeHeat047Base 16 nativeHeat047Y00 = nativeHeat047Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat047Pass16]
  have h20 : nativeHeatPasses nativeGap048Old nativeHeat047Frames nativeHeat047Coef nativeHeat047Fixed nativeHeat047Base 20 nativeHeat047Y00 = nativeHeat047Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat047Pass20]
  have h24 : nativeHeatPasses nativeGap048Old nativeHeat047Frames nativeHeat047Coef nativeHeat047Fixed nativeHeat047Base 24 nativeHeat047Y00 = nativeHeat047Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat047Pass24]
  have h28 : nativeHeatPasses nativeGap048Old nativeHeat047Frames nativeHeat047Coef nativeHeat047Fixed nativeHeat047Base 28 nativeHeat047Y00 = nativeHeat047Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat047Pass28]
  have h32 : nativeHeatPasses nativeGap048Old nativeHeat047Frames nativeHeat047Coef nativeHeat047Fixed nativeHeat047Base 32 nativeHeat047Y00 = nativeHeat047Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat047Pass32]
  have h36 : nativeHeatPasses nativeGap048Old nativeHeat047Frames nativeHeat047Coef nativeHeat047Fixed nativeHeat047Base 36 nativeHeat047Y00 = nativeHeat047Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat047Pass36]
  have h40 : nativeHeatPasses nativeGap048Old nativeHeat047Frames nativeHeat047Coef nativeHeat047Fixed nativeHeat047Base 40 nativeHeat047Y00 = nativeHeat047Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat047Pass40]
  have h44 : nativeHeatPasses nativeGap048Old nativeHeat047Frames nativeHeat047Coef nativeHeat047Fixed nativeHeat047Base 44 nativeHeat047Y00 = nativeHeat047Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat047Pass44]
  have h48 : nativeHeatPasses nativeGap048Old nativeHeat047Frames nativeHeat047Coef nativeHeat047Fixed nativeHeat047Base 48 nativeHeat047Y00 = nativeHeat047Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat047Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
