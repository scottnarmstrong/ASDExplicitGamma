module
public import ASDExplicitGamma.Numerics.Native.Heat123Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat123Y00_formula : nativeHeat123Y00 = nativeHeat123Frames.y := by
  decide +kernel

theorem nativeHeat123All48 : nativeHeatPasses nativeGap124Old nativeHeat123Frames nativeHeat123Coef nativeHeat123Fixed nativeHeat123Base 48 nativeHeat123Frames.y = nativeHeat123Y48 := by
  rw [← nativeHeat123Y00_formula]
  have h4 : nativeHeatPasses nativeGap124Old nativeHeat123Frames nativeHeat123Coef nativeHeat123Fixed nativeHeat123Base 4 nativeHeat123Y00 = nativeHeat123Y04 := nativeHeat123Pass04
  have h8 : nativeHeatPasses nativeGap124Old nativeHeat123Frames nativeHeat123Coef nativeHeat123Fixed nativeHeat123Base 8 nativeHeat123Y00 = nativeHeat123Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat123Pass08]
  have h12 : nativeHeatPasses nativeGap124Old nativeHeat123Frames nativeHeat123Coef nativeHeat123Fixed nativeHeat123Base 12 nativeHeat123Y00 = nativeHeat123Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat123Pass12]
  have h16 : nativeHeatPasses nativeGap124Old nativeHeat123Frames nativeHeat123Coef nativeHeat123Fixed nativeHeat123Base 16 nativeHeat123Y00 = nativeHeat123Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat123Pass16]
  have h20 : nativeHeatPasses nativeGap124Old nativeHeat123Frames nativeHeat123Coef nativeHeat123Fixed nativeHeat123Base 20 nativeHeat123Y00 = nativeHeat123Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat123Pass20]
  have h24 : nativeHeatPasses nativeGap124Old nativeHeat123Frames nativeHeat123Coef nativeHeat123Fixed nativeHeat123Base 24 nativeHeat123Y00 = nativeHeat123Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat123Pass24]
  have h28 : nativeHeatPasses nativeGap124Old nativeHeat123Frames nativeHeat123Coef nativeHeat123Fixed nativeHeat123Base 28 nativeHeat123Y00 = nativeHeat123Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat123Pass28]
  have h32 : nativeHeatPasses nativeGap124Old nativeHeat123Frames nativeHeat123Coef nativeHeat123Fixed nativeHeat123Base 32 nativeHeat123Y00 = nativeHeat123Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat123Pass32]
  have h36 : nativeHeatPasses nativeGap124Old nativeHeat123Frames nativeHeat123Coef nativeHeat123Fixed nativeHeat123Base 36 nativeHeat123Y00 = nativeHeat123Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat123Pass36]
  have h40 : nativeHeatPasses nativeGap124Old nativeHeat123Frames nativeHeat123Coef nativeHeat123Fixed nativeHeat123Base 40 nativeHeat123Y00 = nativeHeat123Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat123Pass40]
  have h44 : nativeHeatPasses nativeGap124Old nativeHeat123Frames nativeHeat123Coef nativeHeat123Fixed nativeHeat123Base 44 nativeHeat123Y00 = nativeHeat123Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat123Pass44]
  have h48 : nativeHeatPasses nativeGap124Old nativeHeat123Frames nativeHeat123Coef nativeHeat123Fixed nativeHeat123Base 48 nativeHeat123Y00 = nativeHeat123Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat123Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
