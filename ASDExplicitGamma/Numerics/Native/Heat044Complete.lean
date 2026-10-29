module
public import ASDExplicitGamma.Numerics.Native.Heat044Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat044Y00_formula : nativeHeat044Y00 = nativeHeat044Frames.y := by
  decide +kernel

theorem nativeHeat044All48 : nativeHeatPasses nativeGap045Old nativeHeat044Frames nativeHeat044Coef nativeHeat044Fixed nativeHeat044Base 48 nativeHeat044Frames.y = nativeHeat044Y48 := by
  rw [← nativeHeat044Y00_formula]
  have h4 : nativeHeatPasses nativeGap045Old nativeHeat044Frames nativeHeat044Coef nativeHeat044Fixed nativeHeat044Base 4 nativeHeat044Y00 = nativeHeat044Y04 := nativeHeat044Pass04
  have h8 : nativeHeatPasses nativeGap045Old nativeHeat044Frames nativeHeat044Coef nativeHeat044Fixed nativeHeat044Base 8 nativeHeat044Y00 = nativeHeat044Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat044Pass08]
  have h12 : nativeHeatPasses nativeGap045Old nativeHeat044Frames nativeHeat044Coef nativeHeat044Fixed nativeHeat044Base 12 nativeHeat044Y00 = nativeHeat044Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat044Pass12]
  have h16 : nativeHeatPasses nativeGap045Old nativeHeat044Frames nativeHeat044Coef nativeHeat044Fixed nativeHeat044Base 16 nativeHeat044Y00 = nativeHeat044Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat044Pass16]
  have h20 : nativeHeatPasses nativeGap045Old nativeHeat044Frames nativeHeat044Coef nativeHeat044Fixed nativeHeat044Base 20 nativeHeat044Y00 = nativeHeat044Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat044Pass20]
  have h24 : nativeHeatPasses nativeGap045Old nativeHeat044Frames nativeHeat044Coef nativeHeat044Fixed nativeHeat044Base 24 nativeHeat044Y00 = nativeHeat044Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat044Pass24]
  have h28 : nativeHeatPasses nativeGap045Old nativeHeat044Frames nativeHeat044Coef nativeHeat044Fixed nativeHeat044Base 28 nativeHeat044Y00 = nativeHeat044Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat044Pass28]
  have h32 : nativeHeatPasses nativeGap045Old nativeHeat044Frames nativeHeat044Coef nativeHeat044Fixed nativeHeat044Base 32 nativeHeat044Y00 = nativeHeat044Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat044Pass32]
  have h36 : nativeHeatPasses nativeGap045Old nativeHeat044Frames nativeHeat044Coef nativeHeat044Fixed nativeHeat044Base 36 nativeHeat044Y00 = nativeHeat044Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat044Pass36]
  have h40 : nativeHeatPasses nativeGap045Old nativeHeat044Frames nativeHeat044Coef nativeHeat044Fixed nativeHeat044Base 40 nativeHeat044Y00 = nativeHeat044Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat044Pass40]
  have h44 : nativeHeatPasses nativeGap045Old nativeHeat044Frames nativeHeat044Coef nativeHeat044Fixed nativeHeat044Base 44 nativeHeat044Y00 = nativeHeat044Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat044Pass44]
  have h48 : nativeHeatPasses nativeGap045Old nativeHeat044Frames nativeHeat044Coef nativeHeat044Fixed nativeHeat044Base 48 nativeHeat044Y00 = nativeHeat044Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat044Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
