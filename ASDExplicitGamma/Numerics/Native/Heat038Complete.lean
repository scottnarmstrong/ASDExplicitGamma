module
public import ASDExplicitGamma.Numerics.Native.Heat038Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat038Y00_formula : nativeHeat038Y00 = nativeHeat038Frames.y := by
  decide +kernel

theorem nativeHeat038All48 : nativeHeatPasses nativeGap039Old nativeHeat038Frames nativeHeat038Coef nativeHeat038Fixed nativeHeat038Base 48 nativeHeat038Frames.y = nativeHeat038Y48 := by
  rw [← nativeHeat038Y00_formula]
  have h4 : nativeHeatPasses nativeGap039Old nativeHeat038Frames nativeHeat038Coef nativeHeat038Fixed nativeHeat038Base 4 nativeHeat038Y00 = nativeHeat038Y04 := nativeHeat038Pass04
  have h8 : nativeHeatPasses nativeGap039Old nativeHeat038Frames nativeHeat038Coef nativeHeat038Fixed nativeHeat038Base 8 nativeHeat038Y00 = nativeHeat038Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat038Pass08]
  have h12 : nativeHeatPasses nativeGap039Old nativeHeat038Frames nativeHeat038Coef nativeHeat038Fixed nativeHeat038Base 12 nativeHeat038Y00 = nativeHeat038Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat038Pass12]
  have h16 : nativeHeatPasses nativeGap039Old nativeHeat038Frames nativeHeat038Coef nativeHeat038Fixed nativeHeat038Base 16 nativeHeat038Y00 = nativeHeat038Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat038Pass16]
  have h20 : nativeHeatPasses nativeGap039Old nativeHeat038Frames nativeHeat038Coef nativeHeat038Fixed nativeHeat038Base 20 nativeHeat038Y00 = nativeHeat038Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat038Pass20]
  have h24 : nativeHeatPasses nativeGap039Old nativeHeat038Frames nativeHeat038Coef nativeHeat038Fixed nativeHeat038Base 24 nativeHeat038Y00 = nativeHeat038Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat038Pass24]
  have h28 : nativeHeatPasses nativeGap039Old nativeHeat038Frames nativeHeat038Coef nativeHeat038Fixed nativeHeat038Base 28 nativeHeat038Y00 = nativeHeat038Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat038Pass28]
  have h32 : nativeHeatPasses nativeGap039Old nativeHeat038Frames nativeHeat038Coef nativeHeat038Fixed nativeHeat038Base 32 nativeHeat038Y00 = nativeHeat038Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat038Pass32]
  have h36 : nativeHeatPasses nativeGap039Old nativeHeat038Frames nativeHeat038Coef nativeHeat038Fixed nativeHeat038Base 36 nativeHeat038Y00 = nativeHeat038Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat038Pass36]
  have h40 : nativeHeatPasses nativeGap039Old nativeHeat038Frames nativeHeat038Coef nativeHeat038Fixed nativeHeat038Base 40 nativeHeat038Y00 = nativeHeat038Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat038Pass40]
  have h44 : nativeHeatPasses nativeGap039Old nativeHeat038Frames nativeHeat038Coef nativeHeat038Fixed nativeHeat038Base 44 nativeHeat038Y00 = nativeHeat038Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat038Pass44]
  have h48 : nativeHeatPasses nativeGap039Old nativeHeat038Frames nativeHeat038Coef nativeHeat038Fixed nativeHeat038Base 48 nativeHeat038Y00 = nativeHeat038Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat038Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
