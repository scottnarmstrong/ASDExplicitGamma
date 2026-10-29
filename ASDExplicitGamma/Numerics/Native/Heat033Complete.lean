module
public import ASDExplicitGamma.Numerics.Native.Heat033Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat033Y00_formula : nativeHeat033Y00 = nativeHeat033Frames.y := by
  decide +kernel

theorem nativeHeat033All48 : nativeHeatPasses nativeGap034Old nativeHeat033Frames nativeHeat033Coef nativeHeat033Fixed nativeHeat033Base 48 nativeHeat033Frames.y = nativeHeat033Y48 := by
  rw [← nativeHeat033Y00_formula]
  have h4 : nativeHeatPasses nativeGap034Old nativeHeat033Frames nativeHeat033Coef nativeHeat033Fixed nativeHeat033Base 4 nativeHeat033Y00 = nativeHeat033Y04 := nativeHeat033Pass04
  have h8 : nativeHeatPasses nativeGap034Old nativeHeat033Frames nativeHeat033Coef nativeHeat033Fixed nativeHeat033Base 8 nativeHeat033Y00 = nativeHeat033Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat033Pass08]
  have h12 : nativeHeatPasses nativeGap034Old nativeHeat033Frames nativeHeat033Coef nativeHeat033Fixed nativeHeat033Base 12 nativeHeat033Y00 = nativeHeat033Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat033Pass12]
  have h16 : nativeHeatPasses nativeGap034Old nativeHeat033Frames nativeHeat033Coef nativeHeat033Fixed nativeHeat033Base 16 nativeHeat033Y00 = nativeHeat033Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat033Pass16]
  have h20 : nativeHeatPasses nativeGap034Old nativeHeat033Frames nativeHeat033Coef nativeHeat033Fixed nativeHeat033Base 20 nativeHeat033Y00 = nativeHeat033Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat033Pass20]
  have h24 : nativeHeatPasses nativeGap034Old nativeHeat033Frames nativeHeat033Coef nativeHeat033Fixed nativeHeat033Base 24 nativeHeat033Y00 = nativeHeat033Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat033Pass24]
  have h28 : nativeHeatPasses nativeGap034Old nativeHeat033Frames nativeHeat033Coef nativeHeat033Fixed nativeHeat033Base 28 nativeHeat033Y00 = nativeHeat033Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat033Pass28]
  have h32 : nativeHeatPasses nativeGap034Old nativeHeat033Frames nativeHeat033Coef nativeHeat033Fixed nativeHeat033Base 32 nativeHeat033Y00 = nativeHeat033Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat033Pass32]
  have h36 : nativeHeatPasses nativeGap034Old nativeHeat033Frames nativeHeat033Coef nativeHeat033Fixed nativeHeat033Base 36 nativeHeat033Y00 = nativeHeat033Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat033Pass36]
  have h40 : nativeHeatPasses nativeGap034Old nativeHeat033Frames nativeHeat033Coef nativeHeat033Fixed nativeHeat033Base 40 nativeHeat033Y00 = nativeHeat033Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat033Pass40]
  have h44 : nativeHeatPasses nativeGap034Old nativeHeat033Frames nativeHeat033Coef nativeHeat033Fixed nativeHeat033Base 44 nativeHeat033Y00 = nativeHeat033Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat033Pass44]
  have h48 : nativeHeatPasses nativeGap034Old nativeHeat033Frames nativeHeat033Coef nativeHeat033Fixed nativeHeat033Base 48 nativeHeat033Y00 = nativeHeat033Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat033Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
