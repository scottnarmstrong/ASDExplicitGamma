module
public import ASDExplicitGamma.Numerics.Native.Heat100Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat100Y00_formula : nativeHeat100Y00 = nativeHeat100Frames.y := by
  decide +kernel

theorem nativeHeat100All48 : nativeHeatPasses nativeGap101Old nativeHeat100Frames nativeHeat100Coef nativeHeat100Fixed nativeHeat100Base 48 nativeHeat100Frames.y = nativeHeat100Y48 := by
  rw [← nativeHeat100Y00_formula]
  have h4 : nativeHeatPasses nativeGap101Old nativeHeat100Frames nativeHeat100Coef nativeHeat100Fixed nativeHeat100Base 4 nativeHeat100Y00 = nativeHeat100Y04 := nativeHeat100Pass04
  have h8 : nativeHeatPasses nativeGap101Old nativeHeat100Frames nativeHeat100Coef nativeHeat100Fixed nativeHeat100Base 8 nativeHeat100Y00 = nativeHeat100Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat100Pass08]
  have h12 : nativeHeatPasses nativeGap101Old nativeHeat100Frames nativeHeat100Coef nativeHeat100Fixed nativeHeat100Base 12 nativeHeat100Y00 = nativeHeat100Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat100Pass12]
  have h16 : nativeHeatPasses nativeGap101Old nativeHeat100Frames nativeHeat100Coef nativeHeat100Fixed nativeHeat100Base 16 nativeHeat100Y00 = nativeHeat100Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat100Pass16]
  have h20 : nativeHeatPasses nativeGap101Old nativeHeat100Frames nativeHeat100Coef nativeHeat100Fixed nativeHeat100Base 20 nativeHeat100Y00 = nativeHeat100Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat100Pass20]
  have h24 : nativeHeatPasses nativeGap101Old nativeHeat100Frames nativeHeat100Coef nativeHeat100Fixed nativeHeat100Base 24 nativeHeat100Y00 = nativeHeat100Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat100Pass24]
  have h28 : nativeHeatPasses nativeGap101Old nativeHeat100Frames nativeHeat100Coef nativeHeat100Fixed nativeHeat100Base 28 nativeHeat100Y00 = nativeHeat100Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat100Pass28]
  have h32 : nativeHeatPasses nativeGap101Old nativeHeat100Frames nativeHeat100Coef nativeHeat100Fixed nativeHeat100Base 32 nativeHeat100Y00 = nativeHeat100Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat100Pass32]
  have h36 : nativeHeatPasses nativeGap101Old nativeHeat100Frames nativeHeat100Coef nativeHeat100Fixed nativeHeat100Base 36 nativeHeat100Y00 = nativeHeat100Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat100Pass36]
  have h40 : nativeHeatPasses nativeGap101Old nativeHeat100Frames nativeHeat100Coef nativeHeat100Fixed nativeHeat100Base 40 nativeHeat100Y00 = nativeHeat100Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat100Pass40]
  have h44 : nativeHeatPasses nativeGap101Old nativeHeat100Frames nativeHeat100Coef nativeHeat100Fixed nativeHeat100Base 44 nativeHeat100Y00 = nativeHeat100Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat100Pass44]
  have h48 : nativeHeatPasses nativeGap101Old nativeHeat100Frames nativeHeat100Coef nativeHeat100Fixed nativeHeat100Base 48 nativeHeat100Y00 = nativeHeat100Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat100Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
