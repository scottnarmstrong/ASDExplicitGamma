module
public import ASDExplicitGamma.Numerics.Native.Heat068Passes
public import ASDExplicitGamma.Numerics.Native.HeatComposition

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeat068Y00_formula : nativeHeat068Y00 = nativeHeat068Frames.y := by
  decide +kernel

theorem nativeHeat068All48 : nativeHeatPasses nativeGap069Old nativeHeat068Frames nativeHeat068Coef nativeHeat068Fixed nativeHeat068Base 48 nativeHeat068Frames.y = nativeHeat068Y48 := by
  rw [← nativeHeat068Y00_formula]
  have h4 : nativeHeatPasses nativeGap069Old nativeHeat068Frames nativeHeat068Coef nativeHeat068Fixed nativeHeat068Base 4 nativeHeat068Y00 = nativeHeat068Y04 := nativeHeat068Pass04
  have h8 : nativeHeatPasses nativeGap069Old nativeHeat068Frames nativeHeat068Coef nativeHeat068Fixed nativeHeat068Base 8 nativeHeat068Y00 = nativeHeat068Y08 := by
    rw [show (8 : ℕ) = 4+4 from rfl,nativeHeatPasses_add,h4,nativeHeat068Pass08]
  have h12 : nativeHeatPasses nativeGap069Old nativeHeat068Frames nativeHeat068Coef nativeHeat068Fixed nativeHeat068Base 12 nativeHeat068Y00 = nativeHeat068Y12 := by
    rw [show (12 : ℕ) = 8+4 from rfl,nativeHeatPasses_add,h8,nativeHeat068Pass12]
  have h16 : nativeHeatPasses nativeGap069Old nativeHeat068Frames nativeHeat068Coef nativeHeat068Fixed nativeHeat068Base 16 nativeHeat068Y00 = nativeHeat068Y16 := by
    rw [show (16 : ℕ) = 12+4 from rfl,nativeHeatPasses_add,h12,nativeHeat068Pass16]
  have h20 : nativeHeatPasses nativeGap069Old nativeHeat068Frames nativeHeat068Coef nativeHeat068Fixed nativeHeat068Base 20 nativeHeat068Y00 = nativeHeat068Y20 := by
    rw [show (20 : ℕ) = 16+4 from rfl,nativeHeatPasses_add,h16,nativeHeat068Pass20]
  have h24 : nativeHeatPasses nativeGap069Old nativeHeat068Frames nativeHeat068Coef nativeHeat068Fixed nativeHeat068Base 24 nativeHeat068Y00 = nativeHeat068Y24 := by
    rw [show (24 : ℕ) = 20+4 from rfl,nativeHeatPasses_add,h20,nativeHeat068Pass24]
  have h28 : nativeHeatPasses nativeGap069Old nativeHeat068Frames nativeHeat068Coef nativeHeat068Fixed nativeHeat068Base 28 nativeHeat068Y00 = nativeHeat068Y28 := by
    rw [show (28 : ℕ) = 24+4 from rfl,nativeHeatPasses_add,h24,nativeHeat068Pass28]
  have h32 : nativeHeatPasses nativeGap069Old nativeHeat068Frames nativeHeat068Coef nativeHeat068Fixed nativeHeat068Base 32 nativeHeat068Y00 = nativeHeat068Y32 := by
    rw [show (32 : ℕ) = 28+4 from rfl,nativeHeatPasses_add,h28,nativeHeat068Pass32]
  have h36 : nativeHeatPasses nativeGap069Old nativeHeat068Frames nativeHeat068Coef nativeHeat068Fixed nativeHeat068Base 36 nativeHeat068Y00 = nativeHeat068Y36 := by
    rw [show (36 : ℕ) = 32+4 from rfl,nativeHeatPasses_add,h32,nativeHeat068Pass36]
  have h40 : nativeHeatPasses nativeGap069Old nativeHeat068Frames nativeHeat068Coef nativeHeat068Fixed nativeHeat068Base 40 nativeHeat068Y00 = nativeHeat068Y40 := by
    rw [show (40 : ℕ) = 36+4 from rfl,nativeHeatPasses_add,h36,nativeHeat068Pass40]
  have h44 : nativeHeatPasses nativeGap069Old nativeHeat068Frames nativeHeat068Coef nativeHeat068Fixed nativeHeat068Base 44 nativeHeat068Y00 = nativeHeat068Y44 := by
    rw [show (44 : ℕ) = 40+4 from rfl,nativeHeatPasses_add,h40,nativeHeat068Pass44]
  have h48 : nativeHeatPasses nativeGap069Old nativeHeat068Frames nativeHeat068Coef nativeHeat068Fixed nativeHeat068Base 48 nativeHeat068Y00 = nativeHeat068Y48 := by
    rw [show (48 : ℕ) = 44+4 from rfl,nativeHeatPasses_add,h44,nativeHeat068Pass48]
  exact h48

end ASDExplicitGamma.Numerics.Native
