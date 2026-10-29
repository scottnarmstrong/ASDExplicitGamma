module
public import ASDExplicitGamma.Numerics.Native.Heat101Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat101Y00_formula : nativeHeat101Y00 = nativeHeat101Frames.y := by
  decide +kernel

theorem nativeHeat101All48 : nativeHeatPasses nativeGap102Old nativeHeat101Frames nativeHeat101Coef nativeHeat101Fixed nativeHeat101Base 48 nativeHeat101Frames.y = nativeHeat101Y48 := by
  rw [← nativeHeat101Y00_formula]
  have h4 : nativeHeatPasses nativeGap102Old nativeHeat101Frames nativeHeat101Coef nativeHeat101Fixed nativeHeat101Base 4 nativeHeat101Y00 = nativeHeat101Y04 := nativeHeat101Pass04
  have h8 : nativeHeatPasses nativeGap102Old nativeHeat101Frames nativeHeat101Coef nativeHeat101Fixed nativeHeat101Base 8 nativeHeat101Y00 = nativeHeat101Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat101Pass08]
  have h12 : nativeHeatPasses nativeGap102Old nativeHeat101Frames nativeHeat101Coef nativeHeat101Fixed nativeHeat101Base 12 nativeHeat101Y00 = nativeHeat101Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat101Pass12]
  have h16 : nativeHeatPasses nativeGap102Old nativeHeat101Frames nativeHeat101Coef nativeHeat101Fixed nativeHeat101Base 16 nativeHeat101Y00 = nativeHeat101Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat101Pass16]
  have h20 : nativeHeatPasses nativeGap102Old nativeHeat101Frames nativeHeat101Coef nativeHeat101Fixed nativeHeat101Base 20 nativeHeat101Y00 = nativeHeat101Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat101Pass20]
  have h24 : nativeHeatPasses nativeGap102Old nativeHeat101Frames nativeHeat101Coef nativeHeat101Fixed nativeHeat101Base 24 nativeHeat101Y00 = nativeHeat101Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat101Pass24]
  have h28 : nativeHeatPasses nativeGap102Old nativeHeat101Frames nativeHeat101Coef nativeHeat101Fixed nativeHeat101Base 28 nativeHeat101Y00 = nativeHeat101Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat101Pass28]
  have h32 : nativeHeatPasses nativeGap102Old nativeHeat101Frames nativeHeat101Coef nativeHeat101Fixed nativeHeat101Base 32 nativeHeat101Y00 = nativeHeat101Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat101Pass32]
  have h36 : nativeHeatPasses nativeGap102Old nativeHeat101Frames nativeHeat101Coef nativeHeat101Fixed nativeHeat101Base 36 nativeHeat101Y00 = nativeHeat101Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat101Pass36]
  have h40 : nativeHeatPasses nativeGap102Old nativeHeat101Frames nativeHeat101Coef nativeHeat101Fixed nativeHeat101Base 40 nativeHeat101Y00 = nativeHeat101Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat101Pass40]
  have h44 : nativeHeatPasses nativeGap102Old nativeHeat101Frames nativeHeat101Coef nativeHeat101Fixed nativeHeat101Base 44 nativeHeat101Y00 = nativeHeat101Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat101Pass44]
  have h48 : nativeHeatPasses nativeGap102Old nativeHeat101Frames nativeHeat101Coef nativeHeat101Fixed nativeHeat101Base 48 nativeHeat101Y00 = nativeHeat101Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat101Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
