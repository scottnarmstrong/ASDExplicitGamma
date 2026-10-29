module
public import ASDExplicitGamma.Numerics.Native.Heat110Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat110Y00_formula : nativeHeat110Y00 = nativeHeat110Frames.y := by
  decide +kernel

theorem nativeHeat110All48 : nativeHeatPasses nativeGap111Old nativeHeat110Frames nativeHeat110Coef nativeHeat110Fixed nativeHeat110Base 48 nativeHeat110Frames.y = nativeHeat110Y48 := by
  rw [← nativeHeat110Y00_formula]
  have h4 : nativeHeatPasses nativeGap111Old nativeHeat110Frames nativeHeat110Coef nativeHeat110Fixed nativeHeat110Base 4 nativeHeat110Y00 = nativeHeat110Y04 := nativeHeat110Pass04
  have h8 : nativeHeatPasses nativeGap111Old nativeHeat110Frames nativeHeat110Coef nativeHeat110Fixed nativeHeat110Base 8 nativeHeat110Y00 = nativeHeat110Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat110Pass08]
  have h12 : nativeHeatPasses nativeGap111Old nativeHeat110Frames nativeHeat110Coef nativeHeat110Fixed nativeHeat110Base 12 nativeHeat110Y00 = nativeHeat110Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat110Pass12]
  have h16 : nativeHeatPasses nativeGap111Old nativeHeat110Frames nativeHeat110Coef nativeHeat110Fixed nativeHeat110Base 16 nativeHeat110Y00 = nativeHeat110Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat110Pass16]
  have h20 : nativeHeatPasses nativeGap111Old nativeHeat110Frames nativeHeat110Coef nativeHeat110Fixed nativeHeat110Base 20 nativeHeat110Y00 = nativeHeat110Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat110Pass20]
  have h24 : nativeHeatPasses nativeGap111Old nativeHeat110Frames nativeHeat110Coef nativeHeat110Fixed nativeHeat110Base 24 nativeHeat110Y00 = nativeHeat110Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat110Pass24]
  have h28 : nativeHeatPasses nativeGap111Old nativeHeat110Frames nativeHeat110Coef nativeHeat110Fixed nativeHeat110Base 28 nativeHeat110Y00 = nativeHeat110Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat110Pass28]
  have h32 : nativeHeatPasses nativeGap111Old nativeHeat110Frames nativeHeat110Coef nativeHeat110Fixed nativeHeat110Base 32 nativeHeat110Y00 = nativeHeat110Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat110Pass32]
  have h36 : nativeHeatPasses nativeGap111Old nativeHeat110Frames nativeHeat110Coef nativeHeat110Fixed nativeHeat110Base 36 nativeHeat110Y00 = nativeHeat110Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat110Pass36]
  have h40 : nativeHeatPasses nativeGap111Old nativeHeat110Frames nativeHeat110Coef nativeHeat110Fixed nativeHeat110Base 40 nativeHeat110Y00 = nativeHeat110Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat110Pass40]
  have h44 : nativeHeatPasses nativeGap111Old nativeHeat110Frames nativeHeat110Coef nativeHeat110Fixed nativeHeat110Base 44 nativeHeat110Y00 = nativeHeat110Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat110Pass44]
  have h48 : nativeHeatPasses nativeGap111Old nativeHeat110Frames nativeHeat110Coef nativeHeat110Fixed nativeHeat110Base 48 nativeHeat110Y00 = nativeHeat110Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat110Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
