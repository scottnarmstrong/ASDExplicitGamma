module

public import ASDExplicitGamma.Native.GenericSourceShellRoot
public import ASDExplicitGamma.Inverse.SourceVarianceClock
public import ASDExplicitGamma.Inverse.SourceCovarianceBudget
public import ASDExplicitGamma.Inverse.RawShellBudget

/-! The actual unrefined finite source-band budget, with complete covariance
sums and the physical clock at the completed starting label. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse
noncomputable section

/-- The physical (unbounded-depth) source variance clock. -/
def nativeSourceShellClock (gamma : ℝ) (height : ℕ) : ℝ :=
  (9/2:ℝ)*gamma*(3:ℝ)^(2*gamma*(height:ℝ))

/-- Every shell in a finite source band obeys the same physical variance clock. -/
theorem native_source_shell_variance_le_clock
    (M : ABKModel 2) (h : ℝ) (n : ℤ) (height s : ℕ)
    (hstate : nativeInductionState M h n) (hs : s ≤ height) :
    (q3ModelAmplitude M h (n+(s:ℤ)))^2/(Annealed.sigmaBar M n:ℝ)^2 ≤
      nativeSourceShellClock M.gamma height := by
  have hh := source_native_shell_variance_clock M h n (n+(s:ℤ)) hstate
  have hsR : (s:ℝ) ≤ (height:ℝ) := by exact_mod_cast hs
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3)
    (mul_le_mul_of_nonneg_left hsR (mul_nonneg (by norm_num : (0:ℝ)≤2) M.shellPrefix.gamma_pos.le))
  have hclock := mul_le_mul_of_nonneg_left hp
    (mul_nonneg (by norm_num : (0:ℝ)≤9/2) M.shellPrefix.gamma_pos.le)
  have hh' : (q3ModelAmplitude M h (n+(s:ℤ)))^2/(Annealed.sigmaBar M n:ℝ)^2 ≤
      (9/2:ℝ)*M.gamma*(3:ℝ)^(2*M.gamma*(s:ℝ)) := by
    simpa only [Int.cast_add,Int.cast_natCast,add_sub_cancel_left] using hh
  exact hh'.trans hclock

end
end ASDExplicitGamma.Native
