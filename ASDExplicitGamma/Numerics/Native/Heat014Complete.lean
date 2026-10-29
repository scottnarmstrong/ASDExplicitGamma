module
public import ASDExplicitGamma.Numerics.Native.Heat014Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat014Y00_formula : nativeHeat014Y00 = nativeHeat014Frames.y := by
  decide +kernel

theorem nativeHeat014All48 : nativeHeatPasses nativeGap015Old nativeHeat014Frames nativeHeat014Coef nativeHeat014Fixed nativeHeat014Base 48 nativeHeat014Frames.y = nativeHeat014Y48 := by
  rw [← nativeHeat014Y00_formula]
  have h4 : nativeHeatPasses nativeGap015Old nativeHeat014Frames nativeHeat014Coef nativeHeat014Fixed nativeHeat014Base 4 nativeHeat014Y00 = nativeHeat014Y04 := nativeHeat014Pass04
  have h8 : nativeHeatPasses nativeGap015Old nativeHeat014Frames nativeHeat014Coef nativeHeat014Fixed nativeHeat014Base 8 nativeHeat014Y00 = nativeHeat014Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat014Pass08]
  have h12 : nativeHeatPasses nativeGap015Old nativeHeat014Frames nativeHeat014Coef nativeHeat014Fixed nativeHeat014Base 12 nativeHeat014Y00 = nativeHeat014Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat014Pass12]
  have h16 : nativeHeatPasses nativeGap015Old nativeHeat014Frames nativeHeat014Coef nativeHeat014Fixed nativeHeat014Base 16 nativeHeat014Y00 = nativeHeat014Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat014Pass16]
  have h20 : nativeHeatPasses nativeGap015Old nativeHeat014Frames nativeHeat014Coef nativeHeat014Fixed nativeHeat014Base 20 nativeHeat014Y00 = nativeHeat014Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat014Pass20]
  have h24 : nativeHeatPasses nativeGap015Old nativeHeat014Frames nativeHeat014Coef nativeHeat014Fixed nativeHeat014Base 24 nativeHeat014Y00 = nativeHeat014Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat014Pass24]
  have h28 : nativeHeatPasses nativeGap015Old nativeHeat014Frames nativeHeat014Coef nativeHeat014Fixed nativeHeat014Base 28 nativeHeat014Y00 = nativeHeat014Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat014Pass28]
  have h32 : nativeHeatPasses nativeGap015Old nativeHeat014Frames nativeHeat014Coef nativeHeat014Fixed nativeHeat014Base 32 nativeHeat014Y00 = nativeHeat014Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat014Pass32]
  have h36 : nativeHeatPasses nativeGap015Old nativeHeat014Frames nativeHeat014Coef nativeHeat014Fixed nativeHeat014Base 36 nativeHeat014Y00 = nativeHeat014Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat014Pass36]
  have h40 : nativeHeatPasses nativeGap015Old nativeHeat014Frames nativeHeat014Coef nativeHeat014Fixed nativeHeat014Base 40 nativeHeat014Y00 = nativeHeat014Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat014Pass40]
  have h44 : nativeHeatPasses nativeGap015Old nativeHeat014Frames nativeHeat014Coef nativeHeat014Fixed nativeHeat014Base 44 nativeHeat014Y00 = nativeHeat014Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat014Pass44]
  have h48 : nativeHeatPasses nativeGap015Old nativeHeat014Frames nativeHeat014Coef nativeHeat014Fixed nativeHeat014Base 48 nativeHeat014Y00 = nativeHeat014Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat014Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
