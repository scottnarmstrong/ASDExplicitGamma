module
public import ASDExplicitGamma.Numerics.Native.Heat108Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat108Y00_formula : nativeHeat108Y00 = nativeHeat108Frames.y := by
  decide +kernel

theorem nativeHeat108All48 : nativeHeatPasses nativeGap109Old nativeHeat108Frames nativeHeat108Coef nativeHeat108Fixed nativeHeat108Base 48 nativeHeat108Frames.y = nativeHeat108Y48 := by
  rw [← nativeHeat108Y00_formula]
  have h4 : nativeHeatPasses nativeGap109Old nativeHeat108Frames nativeHeat108Coef nativeHeat108Fixed nativeHeat108Base 4 nativeHeat108Y00 = nativeHeat108Y04 := nativeHeat108Pass04
  have h8 : nativeHeatPasses nativeGap109Old nativeHeat108Frames nativeHeat108Coef nativeHeat108Fixed nativeHeat108Base 8 nativeHeat108Y00 = nativeHeat108Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat108Pass08]
  have h12 : nativeHeatPasses nativeGap109Old nativeHeat108Frames nativeHeat108Coef nativeHeat108Fixed nativeHeat108Base 12 nativeHeat108Y00 = nativeHeat108Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat108Pass12]
  have h16 : nativeHeatPasses nativeGap109Old nativeHeat108Frames nativeHeat108Coef nativeHeat108Fixed nativeHeat108Base 16 nativeHeat108Y00 = nativeHeat108Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat108Pass16]
  have h20 : nativeHeatPasses nativeGap109Old nativeHeat108Frames nativeHeat108Coef nativeHeat108Fixed nativeHeat108Base 20 nativeHeat108Y00 = nativeHeat108Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat108Pass20]
  have h24 : nativeHeatPasses nativeGap109Old nativeHeat108Frames nativeHeat108Coef nativeHeat108Fixed nativeHeat108Base 24 nativeHeat108Y00 = nativeHeat108Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat108Pass24]
  have h28 : nativeHeatPasses nativeGap109Old nativeHeat108Frames nativeHeat108Coef nativeHeat108Fixed nativeHeat108Base 28 nativeHeat108Y00 = nativeHeat108Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat108Pass28]
  have h32 : nativeHeatPasses nativeGap109Old nativeHeat108Frames nativeHeat108Coef nativeHeat108Fixed nativeHeat108Base 32 nativeHeat108Y00 = nativeHeat108Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat108Pass32]
  have h36 : nativeHeatPasses nativeGap109Old nativeHeat108Frames nativeHeat108Coef nativeHeat108Fixed nativeHeat108Base 36 nativeHeat108Y00 = nativeHeat108Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat108Pass36]
  have h40 : nativeHeatPasses nativeGap109Old nativeHeat108Frames nativeHeat108Coef nativeHeat108Fixed nativeHeat108Base 40 nativeHeat108Y00 = nativeHeat108Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat108Pass40]
  have h44 : nativeHeatPasses nativeGap109Old nativeHeat108Frames nativeHeat108Coef nativeHeat108Fixed nativeHeat108Base 44 nativeHeat108Y00 = nativeHeat108Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat108Pass44]
  have h48 : nativeHeatPasses nativeGap109Old nativeHeat108Frames nativeHeat108Coef nativeHeat108Fixed nativeHeat108Base 48 nativeHeat108Y00 = nativeHeat108Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat108Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
