module
public import ASDExplicitGamma.Numerics.Native.Heat113Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat113Y00_formula : nativeHeat113Y00 = nativeHeat113Frames.y := by
  decide +kernel

theorem nativeHeat113All48 : nativeHeatPasses nativeGap114Old nativeHeat113Frames nativeHeat113Coef nativeHeat113Fixed nativeHeat113Base 48 nativeHeat113Frames.y = nativeHeat113Y48 := by
  rw [← nativeHeat113Y00_formula]
  have h4 : nativeHeatPasses nativeGap114Old nativeHeat113Frames nativeHeat113Coef nativeHeat113Fixed nativeHeat113Base 4 nativeHeat113Y00 = nativeHeat113Y04 := nativeHeat113Pass04
  have h8 : nativeHeatPasses nativeGap114Old nativeHeat113Frames nativeHeat113Coef nativeHeat113Fixed nativeHeat113Base 8 nativeHeat113Y00 = nativeHeat113Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat113Pass08]
  have h12 : nativeHeatPasses nativeGap114Old nativeHeat113Frames nativeHeat113Coef nativeHeat113Fixed nativeHeat113Base 12 nativeHeat113Y00 = nativeHeat113Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat113Pass12]
  have h16 : nativeHeatPasses nativeGap114Old nativeHeat113Frames nativeHeat113Coef nativeHeat113Fixed nativeHeat113Base 16 nativeHeat113Y00 = nativeHeat113Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat113Pass16]
  have h20 : nativeHeatPasses nativeGap114Old nativeHeat113Frames nativeHeat113Coef nativeHeat113Fixed nativeHeat113Base 20 nativeHeat113Y00 = nativeHeat113Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat113Pass20]
  have h24 : nativeHeatPasses nativeGap114Old nativeHeat113Frames nativeHeat113Coef nativeHeat113Fixed nativeHeat113Base 24 nativeHeat113Y00 = nativeHeat113Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat113Pass24]
  have h28 : nativeHeatPasses nativeGap114Old nativeHeat113Frames nativeHeat113Coef nativeHeat113Fixed nativeHeat113Base 28 nativeHeat113Y00 = nativeHeat113Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat113Pass28]
  have h32 : nativeHeatPasses nativeGap114Old nativeHeat113Frames nativeHeat113Coef nativeHeat113Fixed nativeHeat113Base 32 nativeHeat113Y00 = nativeHeat113Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat113Pass32]
  have h36 : nativeHeatPasses nativeGap114Old nativeHeat113Frames nativeHeat113Coef nativeHeat113Fixed nativeHeat113Base 36 nativeHeat113Y00 = nativeHeat113Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat113Pass36]
  have h40 : nativeHeatPasses nativeGap114Old nativeHeat113Frames nativeHeat113Coef nativeHeat113Fixed nativeHeat113Base 40 nativeHeat113Y00 = nativeHeat113Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat113Pass40]
  have h44 : nativeHeatPasses nativeGap114Old nativeHeat113Frames nativeHeat113Coef nativeHeat113Fixed nativeHeat113Base 44 nativeHeat113Y00 = nativeHeat113Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat113Pass44]
  have h48 : nativeHeatPasses nativeGap114Old nativeHeat113Frames nativeHeat113Coef nativeHeat113Fixed nativeHeat113Base 48 nativeHeat113Y00 = nativeHeat113Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat113Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
