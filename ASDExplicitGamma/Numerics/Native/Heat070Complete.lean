module
public import ASDExplicitGamma.Numerics.Native.Heat070Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat070Y00_formula : nativeHeat070Y00 = nativeHeat070Frames.y := by
  decide +kernel

theorem nativeHeat070All48 : nativeHeatPasses nativeGap071Old nativeHeat070Frames nativeHeat070Coef nativeHeat070Fixed nativeHeat070Base 48 nativeHeat070Frames.y = nativeHeat070Y48 := by
  rw [← nativeHeat070Y00_formula]
  have h4 : nativeHeatPasses nativeGap071Old nativeHeat070Frames nativeHeat070Coef nativeHeat070Fixed nativeHeat070Base 4 nativeHeat070Y00 = nativeHeat070Y04 := nativeHeat070Pass04
  have h8 : nativeHeatPasses nativeGap071Old nativeHeat070Frames nativeHeat070Coef nativeHeat070Fixed nativeHeat070Base 8 nativeHeat070Y00 = nativeHeat070Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat070Pass08]
  have h12 : nativeHeatPasses nativeGap071Old nativeHeat070Frames nativeHeat070Coef nativeHeat070Fixed nativeHeat070Base 12 nativeHeat070Y00 = nativeHeat070Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat070Pass12]
  have h16 : nativeHeatPasses nativeGap071Old nativeHeat070Frames nativeHeat070Coef nativeHeat070Fixed nativeHeat070Base 16 nativeHeat070Y00 = nativeHeat070Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat070Pass16]
  have h20 : nativeHeatPasses nativeGap071Old nativeHeat070Frames nativeHeat070Coef nativeHeat070Fixed nativeHeat070Base 20 nativeHeat070Y00 = nativeHeat070Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat070Pass20]
  have h24 : nativeHeatPasses nativeGap071Old nativeHeat070Frames nativeHeat070Coef nativeHeat070Fixed nativeHeat070Base 24 nativeHeat070Y00 = nativeHeat070Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat070Pass24]
  have h28 : nativeHeatPasses nativeGap071Old nativeHeat070Frames nativeHeat070Coef nativeHeat070Fixed nativeHeat070Base 28 nativeHeat070Y00 = nativeHeat070Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat070Pass28]
  have h32 : nativeHeatPasses nativeGap071Old nativeHeat070Frames nativeHeat070Coef nativeHeat070Fixed nativeHeat070Base 32 nativeHeat070Y00 = nativeHeat070Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat070Pass32]
  have h36 : nativeHeatPasses nativeGap071Old nativeHeat070Frames nativeHeat070Coef nativeHeat070Fixed nativeHeat070Base 36 nativeHeat070Y00 = nativeHeat070Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat070Pass36]
  have h40 : nativeHeatPasses nativeGap071Old nativeHeat070Frames nativeHeat070Coef nativeHeat070Fixed nativeHeat070Base 40 nativeHeat070Y00 = nativeHeat070Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat070Pass40]
  have h44 : nativeHeatPasses nativeGap071Old nativeHeat070Frames nativeHeat070Coef nativeHeat070Fixed nativeHeat070Base 44 nativeHeat070Y00 = nativeHeat070Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat070Pass44]
  have h48 : nativeHeatPasses nativeGap071Old nativeHeat070Frames nativeHeat070Coef nativeHeat070Fixed nativeHeat070Base 48 nativeHeat070Y00 = nativeHeat070Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat070Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
