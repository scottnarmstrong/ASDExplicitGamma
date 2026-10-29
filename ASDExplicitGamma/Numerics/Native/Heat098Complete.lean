module
public import ASDExplicitGamma.Numerics.Native.Heat098Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat098Y00_formula : nativeHeat098Y00 = nativeHeat098Frames.y := by
  decide +kernel

theorem nativeHeat098All48 : nativeHeatPasses nativeGap099Old nativeHeat098Frames nativeHeat098Coef nativeHeat098Fixed nativeHeat098Base 48 nativeHeat098Frames.y = nativeHeat098Y48 := by
  rw [← nativeHeat098Y00_formula]
  have h4 : nativeHeatPasses nativeGap099Old nativeHeat098Frames nativeHeat098Coef nativeHeat098Fixed nativeHeat098Base 4 nativeHeat098Y00 = nativeHeat098Y04 := nativeHeat098Pass04
  have h8 : nativeHeatPasses nativeGap099Old nativeHeat098Frames nativeHeat098Coef nativeHeat098Fixed nativeHeat098Base 8 nativeHeat098Y00 = nativeHeat098Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat098Pass08]
  have h12 : nativeHeatPasses nativeGap099Old nativeHeat098Frames nativeHeat098Coef nativeHeat098Fixed nativeHeat098Base 12 nativeHeat098Y00 = nativeHeat098Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat098Pass12]
  have h16 : nativeHeatPasses nativeGap099Old nativeHeat098Frames nativeHeat098Coef nativeHeat098Fixed nativeHeat098Base 16 nativeHeat098Y00 = nativeHeat098Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat098Pass16]
  have h20 : nativeHeatPasses nativeGap099Old nativeHeat098Frames nativeHeat098Coef nativeHeat098Fixed nativeHeat098Base 20 nativeHeat098Y00 = nativeHeat098Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat098Pass20]
  have h24 : nativeHeatPasses nativeGap099Old nativeHeat098Frames nativeHeat098Coef nativeHeat098Fixed nativeHeat098Base 24 nativeHeat098Y00 = nativeHeat098Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat098Pass24]
  have h28 : nativeHeatPasses nativeGap099Old nativeHeat098Frames nativeHeat098Coef nativeHeat098Fixed nativeHeat098Base 28 nativeHeat098Y00 = nativeHeat098Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat098Pass28]
  have h32 : nativeHeatPasses nativeGap099Old nativeHeat098Frames nativeHeat098Coef nativeHeat098Fixed nativeHeat098Base 32 nativeHeat098Y00 = nativeHeat098Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat098Pass32]
  have h36 : nativeHeatPasses nativeGap099Old nativeHeat098Frames nativeHeat098Coef nativeHeat098Fixed nativeHeat098Base 36 nativeHeat098Y00 = nativeHeat098Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat098Pass36]
  have h40 : nativeHeatPasses nativeGap099Old nativeHeat098Frames nativeHeat098Coef nativeHeat098Fixed nativeHeat098Base 40 nativeHeat098Y00 = nativeHeat098Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat098Pass40]
  have h44 : nativeHeatPasses nativeGap099Old nativeHeat098Frames nativeHeat098Coef nativeHeat098Fixed nativeHeat098Base 44 nativeHeat098Y00 = nativeHeat098Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat098Pass44]
  have h48 : nativeHeatPasses nativeGap099Old nativeHeat098Frames nativeHeat098Coef nativeHeat098Fixed nativeHeat098Base 48 nativeHeat098Y00 = nativeHeat098Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat098Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
