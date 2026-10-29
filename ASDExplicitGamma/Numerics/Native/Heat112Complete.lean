module
public import ASDExplicitGamma.Numerics.Native.Heat112Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat112Y00_formula : nativeHeat112Y00 = nativeHeat112Frames.y := by
  decide +kernel

theorem nativeHeat112All48 : nativeHeatPasses nativeGap113Old nativeHeat112Frames nativeHeat112Coef nativeHeat112Fixed nativeHeat112Base 48 nativeHeat112Frames.y = nativeHeat112Y48 := by
  rw [← nativeHeat112Y00_formula]
  have h4 : nativeHeatPasses nativeGap113Old nativeHeat112Frames nativeHeat112Coef nativeHeat112Fixed nativeHeat112Base 4 nativeHeat112Y00 = nativeHeat112Y04 := nativeHeat112Pass04
  have h8 : nativeHeatPasses nativeGap113Old nativeHeat112Frames nativeHeat112Coef nativeHeat112Fixed nativeHeat112Base 8 nativeHeat112Y00 = nativeHeat112Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat112Pass08]
  have h12 : nativeHeatPasses nativeGap113Old nativeHeat112Frames nativeHeat112Coef nativeHeat112Fixed nativeHeat112Base 12 nativeHeat112Y00 = nativeHeat112Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat112Pass12]
  have h16 : nativeHeatPasses nativeGap113Old nativeHeat112Frames nativeHeat112Coef nativeHeat112Fixed nativeHeat112Base 16 nativeHeat112Y00 = nativeHeat112Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat112Pass16]
  have h20 : nativeHeatPasses nativeGap113Old nativeHeat112Frames nativeHeat112Coef nativeHeat112Fixed nativeHeat112Base 20 nativeHeat112Y00 = nativeHeat112Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat112Pass20]
  have h24 : nativeHeatPasses nativeGap113Old nativeHeat112Frames nativeHeat112Coef nativeHeat112Fixed nativeHeat112Base 24 nativeHeat112Y00 = nativeHeat112Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat112Pass24]
  have h28 : nativeHeatPasses nativeGap113Old nativeHeat112Frames nativeHeat112Coef nativeHeat112Fixed nativeHeat112Base 28 nativeHeat112Y00 = nativeHeat112Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat112Pass28]
  have h32 : nativeHeatPasses nativeGap113Old nativeHeat112Frames nativeHeat112Coef nativeHeat112Fixed nativeHeat112Base 32 nativeHeat112Y00 = nativeHeat112Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat112Pass32]
  have h36 : nativeHeatPasses nativeGap113Old nativeHeat112Frames nativeHeat112Coef nativeHeat112Fixed nativeHeat112Base 36 nativeHeat112Y00 = nativeHeat112Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat112Pass36]
  have h40 : nativeHeatPasses nativeGap113Old nativeHeat112Frames nativeHeat112Coef nativeHeat112Fixed nativeHeat112Base 40 nativeHeat112Y00 = nativeHeat112Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat112Pass40]
  have h44 : nativeHeatPasses nativeGap113Old nativeHeat112Frames nativeHeat112Coef nativeHeat112Fixed nativeHeat112Base 44 nativeHeat112Y00 = nativeHeat112Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat112Pass44]
  have h48 : nativeHeatPasses nativeGap113Old nativeHeat112Frames nativeHeat112Coef nativeHeat112Fixed nativeHeat112Base 48 nativeHeat112Y00 = nativeHeat112Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat112Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
