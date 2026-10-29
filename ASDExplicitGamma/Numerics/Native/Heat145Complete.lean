module
public import ASDExplicitGamma.Numerics.Native.Heat145Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat145Y00_formula : nativeHeat145Y00 = nativeHeat145Frames.y := by
  decide +kernel

theorem nativeHeat145All48 : nativeHeatPasses nativeGap146Old nativeHeat145Frames nativeHeat145Coef nativeHeat145Fixed nativeHeat145Base 48 nativeHeat145Frames.y = nativeHeat145Y48 := by
  rw [← nativeHeat145Y00_formula]
  have h4 : nativeHeatPasses nativeGap146Old nativeHeat145Frames nativeHeat145Coef nativeHeat145Fixed nativeHeat145Base 4 nativeHeat145Y00 = nativeHeat145Y04 := nativeHeat145Pass04
  have h8 : nativeHeatPasses nativeGap146Old nativeHeat145Frames nativeHeat145Coef nativeHeat145Fixed nativeHeat145Base 8 nativeHeat145Y00 = nativeHeat145Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat145Pass08]
  have h12 : nativeHeatPasses nativeGap146Old nativeHeat145Frames nativeHeat145Coef nativeHeat145Fixed nativeHeat145Base 12 nativeHeat145Y00 = nativeHeat145Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat145Pass12]
  have h16 : nativeHeatPasses nativeGap146Old nativeHeat145Frames nativeHeat145Coef nativeHeat145Fixed nativeHeat145Base 16 nativeHeat145Y00 = nativeHeat145Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat145Pass16]
  have h20 : nativeHeatPasses nativeGap146Old nativeHeat145Frames nativeHeat145Coef nativeHeat145Fixed nativeHeat145Base 20 nativeHeat145Y00 = nativeHeat145Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat145Pass20]
  have h24 : nativeHeatPasses nativeGap146Old nativeHeat145Frames nativeHeat145Coef nativeHeat145Fixed nativeHeat145Base 24 nativeHeat145Y00 = nativeHeat145Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat145Pass24]
  have h28 : nativeHeatPasses nativeGap146Old nativeHeat145Frames nativeHeat145Coef nativeHeat145Fixed nativeHeat145Base 28 nativeHeat145Y00 = nativeHeat145Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat145Pass28]
  have h32 : nativeHeatPasses nativeGap146Old nativeHeat145Frames nativeHeat145Coef nativeHeat145Fixed nativeHeat145Base 32 nativeHeat145Y00 = nativeHeat145Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat145Pass32]
  have h36 : nativeHeatPasses nativeGap146Old nativeHeat145Frames nativeHeat145Coef nativeHeat145Fixed nativeHeat145Base 36 nativeHeat145Y00 = nativeHeat145Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat145Pass36]
  have h40 : nativeHeatPasses nativeGap146Old nativeHeat145Frames nativeHeat145Coef nativeHeat145Fixed nativeHeat145Base 40 nativeHeat145Y00 = nativeHeat145Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat145Pass40]
  have h44 : nativeHeatPasses nativeGap146Old nativeHeat145Frames nativeHeat145Coef nativeHeat145Fixed nativeHeat145Base 44 nativeHeat145Y00 = nativeHeat145Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat145Pass44]
  have h48 : nativeHeatPasses nativeGap146Old nativeHeat145Frames nativeHeat145Coef nativeHeat145Fixed nativeHeat145Base 48 nativeHeat145Y00 = nativeHeat145Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat145Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
