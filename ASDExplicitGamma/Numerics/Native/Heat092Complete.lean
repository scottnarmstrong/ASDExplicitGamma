module
public import ASDExplicitGamma.Numerics.Native.Heat092Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat092Y00_formula : nativeHeat092Y00 = nativeHeat092Frames.y := by
  decide +kernel

theorem nativeHeat092All48 : nativeHeatPasses nativeGap093Old nativeHeat092Frames nativeHeat092Coef nativeHeat092Fixed nativeHeat092Base 48 nativeHeat092Frames.y = nativeHeat092Y48 := by
  rw [← nativeHeat092Y00_formula]
  have h4 : nativeHeatPasses nativeGap093Old nativeHeat092Frames nativeHeat092Coef nativeHeat092Fixed nativeHeat092Base 4 nativeHeat092Y00 = nativeHeat092Y04 := nativeHeat092Pass04
  have h8 : nativeHeatPasses nativeGap093Old nativeHeat092Frames nativeHeat092Coef nativeHeat092Fixed nativeHeat092Base 8 nativeHeat092Y00 = nativeHeat092Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat092Pass08]
  have h12 : nativeHeatPasses nativeGap093Old nativeHeat092Frames nativeHeat092Coef nativeHeat092Fixed nativeHeat092Base 12 nativeHeat092Y00 = nativeHeat092Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat092Pass12]
  have h16 : nativeHeatPasses nativeGap093Old nativeHeat092Frames nativeHeat092Coef nativeHeat092Fixed nativeHeat092Base 16 nativeHeat092Y00 = nativeHeat092Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat092Pass16]
  have h20 : nativeHeatPasses nativeGap093Old nativeHeat092Frames nativeHeat092Coef nativeHeat092Fixed nativeHeat092Base 20 nativeHeat092Y00 = nativeHeat092Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat092Pass20]
  have h24 : nativeHeatPasses nativeGap093Old nativeHeat092Frames nativeHeat092Coef nativeHeat092Fixed nativeHeat092Base 24 nativeHeat092Y00 = nativeHeat092Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat092Pass24]
  have h28 : nativeHeatPasses nativeGap093Old nativeHeat092Frames nativeHeat092Coef nativeHeat092Fixed nativeHeat092Base 28 nativeHeat092Y00 = nativeHeat092Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat092Pass28]
  have h32 : nativeHeatPasses nativeGap093Old nativeHeat092Frames nativeHeat092Coef nativeHeat092Fixed nativeHeat092Base 32 nativeHeat092Y00 = nativeHeat092Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat092Pass32]
  have h36 : nativeHeatPasses nativeGap093Old nativeHeat092Frames nativeHeat092Coef nativeHeat092Fixed nativeHeat092Base 36 nativeHeat092Y00 = nativeHeat092Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat092Pass36]
  have h40 : nativeHeatPasses nativeGap093Old nativeHeat092Frames nativeHeat092Coef nativeHeat092Fixed nativeHeat092Base 40 nativeHeat092Y00 = nativeHeat092Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat092Pass40]
  have h44 : nativeHeatPasses nativeGap093Old nativeHeat092Frames nativeHeat092Coef nativeHeat092Fixed nativeHeat092Base 44 nativeHeat092Y00 = nativeHeat092Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat092Pass44]
  have h48 : nativeHeatPasses nativeGap093Old nativeHeat092Frames nativeHeat092Coef nativeHeat092Fixed nativeHeat092Base 48 nativeHeat092Y00 = nativeHeat092Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat092Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
