module
public import ASDExplicitGamma.Numerics.Native.Heat148Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat148Y00_formula : nativeHeat148Y00 = nativeHeat148Frames.y := by
  decide +kernel

theorem nativeHeat148All48 : nativeHeatPasses nativeGap149Old nativeHeat148Frames nativeHeat148Coef nativeHeat148Fixed nativeHeat148Base 48 nativeHeat148Frames.y = nativeHeat148Y48 := by
  rw [← nativeHeat148Y00_formula]
  have h4 : nativeHeatPasses nativeGap149Old nativeHeat148Frames nativeHeat148Coef nativeHeat148Fixed nativeHeat148Base 4 nativeHeat148Y00 = nativeHeat148Y04 := nativeHeat148Pass04
  have h8 : nativeHeatPasses nativeGap149Old nativeHeat148Frames nativeHeat148Coef nativeHeat148Fixed nativeHeat148Base 8 nativeHeat148Y00 = nativeHeat148Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat148Pass08]
  have h12 : nativeHeatPasses nativeGap149Old nativeHeat148Frames nativeHeat148Coef nativeHeat148Fixed nativeHeat148Base 12 nativeHeat148Y00 = nativeHeat148Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat148Pass12]
  have h16 : nativeHeatPasses nativeGap149Old nativeHeat148Frames nativeHeat148Coef nativeHeat148Fixed nativeHeat148Base 16 nativeHeat148Y00 = nativeHeat148Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat148Pass16]
  have h20 : nativeHeatPasses nativeGap149Old nativeHeat148Frames nativeHeat148Coef nativeHeat148Fixed nativeHeat148Base 20 nativeHeat148Y00 = nativeHeat148Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat148Pass20]
  have h24 : nativeHeatPasses nativeGap149Old nativeHeat148Frames nativeHeat148Coef nativeHeat148Fixed nativeHeat148Base 24 nativeHeat148Y00 = nativeHeat148Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat148Pass24]
  have h28 : nativeHeatPasses nativeGap149Old nativeHeat148Frames nativeHeat148Coef nativeHeat148Fixed nativeHeat148Base 28 nativeHeat148Y00 = nativeHeat148Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat148Pass28]
  have h32 : nativeHeatPasses nativeGap149Old nativeHeat148Frames nativeHeat148Coef nativeHeat148Fixed nativeHeat148Base 32 nativeHeat148Y00 = nativeHeat148Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat148Pass32]
  have h36 : nativeHeatPasses nativeGap149Old nativeHeat148Frames nativeHeat148Coef nativeHeat148Fixed nativeHeat148Base 36 nativeHeat148Y00 = nativeHeat148Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat148Pass36]
  have h40 : nativeHeatPasses nativeGap149Old nativeHeat148Frames nativeHeat148Coef nativeHeat148Fixed nativeHeat148Base 40 nativeHeat148Y00 = nativeHeat148Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat148Pass40]
  have h44 : nativeHeatPasses nativeGap149Old nativeHeat148Frames nativeHeat148Coef nativeHeat148Fixed nativeHeat148Base 44 nativeHeat148Y00 = nativeHeat148Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat148Pass44]
  have h48 : nativeHeatPasses nativeGap149Old nativeHeat148Frames nativeHeat148Coef nativeHeat148Fixed nativeHeat148Base 48 nativeHeat148Y00 = nativeHeat148Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat148Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
