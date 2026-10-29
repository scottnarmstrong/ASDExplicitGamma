module
public import ASDExplicitGamma.Numerics.Native.Heat124Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat124Y00_formula : nativeHeat124Y00 = nativeHeat124Frames.y := by
  decide +kernel

theorem nativeHeat124All48 : nativeHeatPasses nativeGap125Old nativeHeat124Frames nativeHeat124Coef nativeHeat124Fixed nativeHeat124Base 48 nativeHeat124Frames.y = nativeHeat124Y48 := by
  rw [← nativeHeat124Y00_formula]
  have h4 : nativeHeatPasses nativeGap125Old nativeHeat124Frames nativeHeat124Coef nativeHeat124Fixed nativeHeat124Base 4 nativeHeat124Y00 = nativeHeat124Y04 := nativeHeat124Pass04
  have h8 : nativeHeatPasses nativeGap125Old nativeHeat124Frames nativeHeat124Coef nativeHeat124Fixed nativeHeat124Base 8 nativeHeat124Y00 = nativeHeat124Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat124Pass08]
  have h12 : nativeHeatPasses nativeGap125Old nativeHeat124Frames nativeHeat124Coef nativeHeat124Fixed nativeHeat124Base 12 nativeHeat124Y00 = nativeHeat124Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat124Pass12]
  have h16 : nativeHeatPasses nativeGap125Old nativeHeat124Frames nativeHeat124Coef nativeHeat124Fixed nativeHeat124Base 16 nativeHeat124Y00 = nativeHeat124Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat124Pass16]
  have h20 : nativeHeatPasses nativeGap125Old nativeHeat124Frames nativeHeat124Coef nativeHeat124Fixed nativeHeat124Base 20 nativeHeat124Y00 = nativeHeat124Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat124Pass20]
  have h24 : nativeHeatPasses nativeGap125Old nativeHeat124Frames nativeHeat124Coef nativeHeat124Fixed nativeHeat124Base 24 nativeHeat124Y00 = nativeHeat124Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat124Pass24]
  have h28 : nativeHeatPasses nativeGap125Old nativeHeat124Frames nativeHeat124Coef nativeHeat124Fixed nativeHeat124Base 28 nativeHeat124Y00 = nativeHeat124Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat124Pass28]
  have h32 : nativeHeatPasses nativeGap125Old nativeHeat124Frames nativeHeat124Coef nativeHeat124Fixed nativeHeat124Base 32 nativeHeat124Y00 = nativeHeat124Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat124Pass32]
  have h36 : nativeHeatPasses nativeGap125Old nativeHeat124Frames nativeHeat124Coef nativeHeat124Fixed nativeHeat124Base 36 nativeHeat124Y00 = nativeHeat124Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat124Pass36]
  have h40 : nativeHeatPasses nativeGap125Old nativeHeat124Frames nativeHeat124Coef nativeHeat124Fixed nativeHeat124Base 40 nativeHeat124Y00 = nativeHeat124Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat124Pass40]
  have h44 : nativeHeatPasses nativeGap125Old nativeHeat124Frames nativeHeat124Coef nativeHeat124Fixed nativeHeat124Base 44 nativeHeat124Y00 = nativeHeat124Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat124Pass44]
  have h48 : nativeHeatPasses nativeGap125Old nativeHeat124Frames nativeHeat124Coef nativeHeat124Fixed nativeHeat124Base 48 nativeHeat124Y00 = nativeHeat124Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat124Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
