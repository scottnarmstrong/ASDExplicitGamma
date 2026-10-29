module
public import ASDExplicitGamma.Numerics.Native.Heat040Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat040Y00_formula : nativeHeat040Y00 = nativeHeat040Frames.y := by
  decide +kernel

theorem nativeHeat040All48 : nativeHeatPasses nativeGap041Old nativeHeat040Frames nativeHeat040Coef nativeHeat040Fixed nativeHeat040Base 48 nativeHeat040Frames.y = nativeHeat040Y48 := by
  rw [← nativeHeat040Y00_formula]
  have h4 : nativeHeatPasses nativeGap041Old nativeHeat040Frames nativeHeat040Coef nativeHeat040Fixed nativeHeat040Base 4 nativeHeat040Y00 = nativeHeat040Y04 := nativeHeat040Pass04
  have h8 : nativeHeatPasses nativeGap041Old nativeHeat040Frames nativeHeat040Coef nativeHeat040Fixed nativeHeat040Base 8 nativeHeat040Y00 = nativeHeat040Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat040Pass08]
  have h12 : nativeHeatPasses nativeGap041Old nativeHeat040Frames nativeHeat040Coef nativeHeat040Fixed nativeHeat040Base 12 nativeHeat040Y00 = nativeHeat040Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat040Pass12]
  have h16 : nativeHeatPasses nativeGap041Old nativeHeat040Frames nativeHeat040Coef nativeHeat040Fixed nativeHeat040Base 16 nativeHeat040Y00 = nativeHeat040Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat040Pass16]
  have h20 : nativeHeatPasses nativeGap041Old nativeHeat040Frames nativeHeat040Coef nativeHeat040Fixed nativeHeat040Base 20 nativeHeat040Y00 = nativeHeat040Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat040Pass20]
  have h24 : nativeHeatPasses nativeGap041Old nativeHeat040Frames nativeHeat040Coef nativeHeat040Fixed nativeHeat040Base 24 nativeHeat040Y00 = nativeHeat040Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat040Pass24]
  have h28 : nativeHeatPasses nativeGap041Old nativeHeat040Frames nativeHeat040Coef nativeHeat040Fixed nativeHeat040Base 28 nativeHeat040Y00 = nativeHeat040Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat040Pass28]
  have h32 : nativeHeatPasses nativeGap041Old nativeHeat040Frames nativeHeat040Coef nativeHeat040Fixed nativeHeat040Base 32 nativeHeat040Y00 = nativeHeat040Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat040Pass32]
  have h36 : nativeHeatPasses nativeGap041Old nativeHeat040Frames nativeHeat040Coef nativeHeat040Fixed nativeHeat040Base 36 nativeHeat040Y00 = nativeHeat040Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat040Pass36]
  have h40 : nativeHeatPasses nativeGap041Old nativeHeat040Frames nativeHeat040Coef nativeHeat040Fixed nativeHeat040Base 40 nativeHeat040Y00 = nativeHeat040Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat040Pass40]
  have h44 : nativeHeatPasses nativeGap041Old nativeHeat040Frames nativeHeat040Coef nativeHeat040Fixed nativeHeat040Base 44 nativeHeat040Y00 = nativeHeat040Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat040Pass44]
  have h48 : nativeHeatPasses nativeGap041Old nativeHeat040Frames nativeHeat040Coef nativeHeat040Fixed nativeHeat040Base 48 nativeHeat040Y00 = nativeHeat040Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat040Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
