module
public import ASDExplicitGamma.Numerics.Native.Heat090Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat090Y00_formula : nativeHeat090Y00 = nativeHeat090Frames.y := by
  decide +kernel

theorem nativeHeat090All48 : nativeHeatPasses nativeGap091Old nativeHeat090Frames nativeHeat090Coef nativeHeat090Fixed nativeHeat090Base 48 nativeHeat090Frames.y = nativeHeat090Y48 := by
  rw [← nativeHeat090Y00_formula]
  have h4 : nativeHeatPasses nativeGap091Old nativeHeat090Frames nativeHeat090Coef nativeHeat090Fixed nativeHeat090Base 4 nativeHeat090Y00 = nativeHeat090Y04 := nativeHeat090Pass04
  have h8 : nativeHeatPasses nativeGap091Old nativeHeat090Frames nativeHeat090Coef nativeHeat090Fixed nativeHeat090Base 8 nativeHeat090Y00 = nativeHeat090Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat090Pass08]
  have h12 : nativeHeatPasses nativeGap091Old nativeHeat090Frames nativeHeat090Coef nativeHeat090Fixed nativeHeat090Base 12 nativeHeat090Y00 = nativeHeat090Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat090Pass12]
  have h16 : nativeHeatPasses nativeGap091Old nativeHeat090Frames nativeHeat090Coef nativeHeat090Fixed nativeHeat090Base 16 nativeHeat090Y00 = nativeHeat090Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat090Pass16]
  have h20 : nativeHeatPasses nativeGap091Old nativeHeat090Frames nativeHeat090Coef nativeHeat090Fixed nativeHeat090Base 20 nativeHeat090Y00 = nativeHeat090Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat090Pass20]
  have h24 : nativeHeatPasses nativeGap091Old nativeHeat090Frames nativeHeat090Coef nativeHeat090Fixed nativeHeat090Base 24 nativeHeat090Y00 = nativeHeat090Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat090Pass24]
  have h28 : nativeHeatPasses nativeGap091Old nativeHeat090Frames nativeHeat090Coef nativeHeat090Fixed nativeHeat090Base 28 nativeHeat090Y00 = nativeHeat090Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat090Pass28]
  have h32 : nativeHeatPasses nativeGap091Old nativeHeat090Frames nativeHeat090Coef nativeHeat090Fixed nativeHeat090Base 32 nativeHeat090Y00 = nativeHeat090Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat090Pass32]
  have h36 : nativeHeatPasses nativeGap091Old nativeHeat090Frames nativeHeat090Coef nativeHeat090Fixed nativeHeat090Base 36 nativeHeat090Y00 = nativeHeat090Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat090Pass36]
  have h40 : nativeHeatPasses nativeGap091Old nativeHeat090Frames nativeHeat090Coef nativeHeat090Fixed nativeHeat090Base 40 nativeHeat090Y00 = nativeHeat090Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat090Pass40]
  have h44 : nativeHeatPasses nativeGap091Old nativeHeat090Frames nativeHeat090Coef nativeHeat090Fixed nativeHeat090Base 44 nativeHeat090Y00 = nativeHeat090Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat090Pass44]
  have h48 : nativeHeatPasses nativeGap091Old nativeHeat090Frames nativeHeat090Coef nativeHeat090Fixed nativeHeat090Base 48 nativeHeat090Y00 = nativeHeat090Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat090Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
