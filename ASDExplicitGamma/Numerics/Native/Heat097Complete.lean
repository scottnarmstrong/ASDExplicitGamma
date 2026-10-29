module
public import ASDExplicitGamma.Numerics.Native.Heat097Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat097Y00_formula : nativeHeat097Y00 = nativeHeat097Frames.y := by
  decide +kernel

theorem nativeHeat097All48 : nativeHeatPasses nativeGap098Old nativeHeat097Frames nativeHeat097Coef nativeHeat097Fixed nativeHeat097Base 48 nativeHeat097Frames.y = nativeHeat097Y48 := by
  rw [← nativeHeat097Y00_formula]
  have h4 : nativeHeatPasses nativeGap098Old nativeHeat097Frames nativeHeat097Coef nativeHeat097Fixed nativeHeat097Base 4 nativeHeat097Y00 = nativeHeat097Y04 := nativeHeat097Pass04
  have h8 : nativeHeatPasses nativeGap098Old nativeHeat097Frames nativeHeat097Coef nativeHeat097Fixed nativeHeat097Base 8 nativeHeat097Y00 = nativeHeat097Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat097Pass08]
  have h12 : nativeHeatPasses nativeGap098Old nativeHeat097Frames nativeHeat097Coef nativeHeat097Fixed nativeHeat097Base 12 nativeHeat097Y00 = nativeHeat097Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat097Pass12]
  have h16 : nativeHeatPasses nativeGap098Old nativeHeat097Frames nativeHeat097Coef nativeHeat097Fixed nativeHeat097Base 16 nativeHeat097Y00 = nativeHeat097Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat097Pass16]
  have h20 : nativeHeatPasses nativeGap098Old nativeHeat097Frames nativeHeat097Coef nativeHeat097Fixed nativeHeat097Base 20 nativeHeat097Y00 = nativeHeat097Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat097Pass20]
  have h24 : nativeHeatPasses nativeGap098Old nativeHeat097Frames nativeHeat097Coef nativeHeat097Fixed nativeHeat097Base 24 nativeHeat097Y00 = nativeHeat097Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat097Pass24]
  have h28 : nativeHeatPasses nativeGap098Old nativeHeat097Frames nativeHeat097Coef nativeHeat097Fixed nativeHeat097Base 28 nativeHeat097Y00 = nativeHeat097Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat097Pass28]
  have h32 : nativeHeatPasses nativeGap098Old nativeHeat097Frames nativeHeat097Coef nativeHeat097Fixed nativeHeat097Base 32 nativeHeat097Y00 = nativeHeat097Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat097Pass32]
  have h36 : nativeHeatPasses nativeGap098Old nativeHeat097Frames nativeHeat097Coef nativeHeat097Fixed nativeHeat097Base 36 nativeHeat097Y00 = nativeHeat097Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat097Pass36]
  have h40 : nativeHeatPasses nativeGap098Old nativeHeat097Frames nativeHeat097Coef nativeHeat097Fixed nativeHeat097Base 40 nativeHeat097Y00 = nativeHeat097Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat097Pass40]
  have h44 : nativeHeatPasses nativeGap098Old nativeHeat097Frames nativeHeat097Coef nativeHeat097Fixed nativeHeat097Base 44 nativeHeat097Y00 = nativeHeat097Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat097Pass44]
  have h48 : nativeHeatPasses nativeGap098Old nativeHeat097Frames nativeHeat097Coef nativeHeat097Fixed nativeHeat097Base 48 nativeHeat097Y00 = nativeHeat097Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat097Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
