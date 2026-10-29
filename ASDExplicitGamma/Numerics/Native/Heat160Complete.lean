module
public import ASDExplicitGamma.Numerics.Native.Heat160Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat160Y00_formula : nativeHeat160Y00 = nativeHeat160Frames.y := by
  decide +kernel

theorem nativeHeat160All48 : nativeHeatPasses nativeGap161Old nativeHeat160Frames nativeHeat160Coef nativeHeat160Fixed nativeHeat160Base 48 nativeHeat160Frames.y = nativeHeat160Y48 := by
  rw [← nativeHeat160Y00_formula]
  have h4 : nativeHeatPasses nativeGap161Old nativeHeat160Frames nativeHeat160Coef nativeHeat160Fixed nativeHeat160Base 4 nativeHeat160Y00 = nativeHeat160Y04 := nativeHeat160Pass04
  have h8 : nativeHeatPasses nativeGap161Old nativeHeat160Frames nativeHeat160Coef nativeHeat160Fixed nativeHeat160Base 8 nativeHeat160Y00 = nativeHeat160Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat160Pass08]
  have h12 : nativeHeatPasses nativeGap161Old nativeHeat160Frames nativeHeat160Coef nativeHeat160Fixed nativeHeat160Base 12 nativeHeat160Y00 = nativeHeat160Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat160Pass12]
  have h16 : nativeHeatPasses nativeGap161Old nativeHeat160Frames nativeHeat160Coef nativeHeat160Fixed nativeHeat160Base 16 nativeHeat160Y00 = nativeHeat160Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat160Pass16]
  have h20 : nativeHeatPasses nativeGap161Old nativeHeat160Frames nativeHeat160Coef nativeHeat160Fixed nativeHeat160Base 20 nativeHeat160Y00 = nativeHeat160Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat160Pass20]
  have h24 : nativeHeatPasses nativeGap161Old nativeHeat160Frames nativeHeat160Coef nativeHeat160Fixed nativeHeat160Base 24 nativeHeat160Y00 = nativeHeat160Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat160Pass24]
  have h28 : nativeHeatPasses nativeGap161Old nativeHeat160Frames nativeHeat160Coef nativeHeat160Fixed nativeHeat160Base 28 nativeHeat160Y00 = nativeHeat160Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat160Pass28]
  have h32 : nativeHeatPasses nativeGap161Old nativeHeat160Frames nativeHeat160Coef nativeHeat160Fixed nativeHeat160Base 32 nativeHeat160Y00 = nativeHeat160Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat160Pass32]
  have h36 : nativeHeatPasses nativeGap161Old nativeHeat160Frames nativeHeat160Coef nativeHeat160Fixed nativeHeat160Base 36 nativeHeat160Y00 = nativeHeat160Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat160Pass36]
  have h40 : nativeHeatPasses nativeGap161Old nativeHeat160Frames nativeHeat160Coef nativeHeat160Fixed nativeHeat160Base 40 nativeHeat160Y00 = nativeHeat160Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat160Pass40]
  have h44 : nativeHeatPasses nativeGap161Old nativeHeat160Frames nativeHeat160Coef nativeHeat160Fixed nativeHeat160Base 44 nativeHeat160Y00 = nativeHeat160Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat160Pass44]
  have h48 : nativeHeatPasses nativeGap161Old nativeHeat160Frames nativeHeat160Coef nativeHeat160Fixed nativeHeat160Base 48 nativeHeat160Y00 = nativeHeat160Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat160Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
