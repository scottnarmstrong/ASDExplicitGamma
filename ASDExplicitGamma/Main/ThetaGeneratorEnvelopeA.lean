module

public import ASDExplicitGamma.Inverse.SourceInterfaceTransport
public import ASDExplicitGamma.Inverse.SourceInterfaceEnergy
public import ASDExplicitGamma.Main.SourcePrefixGates
public import ASDExplicitGamma.Native.SourceRowsInterface
public import ASDExplicitGamma.Cold.NativeThetaScaling
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Actual-law endpoint adapter for the main-return OLD mean envelope. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Inverse ASDExplicitGamma.Native
open ASDExplicitGamma.Numerics.MainReturn

/-- The actual cutoff-law source mean at depth five, in the OLD true frame
`sigmaBar M m` throughout the partial insertion. -/
noncomputable abbrev mainMeanActual_Th (M : ABKModel 2) (m : ℤ) (t : ℝ) : ℝ :=
  inSourceMeanActual M m 5 t

/-- At zero insertion, the actual partial-law source mean is the completed
cutoff-law source row, with its ENNReal expectation converted to `ℝ`. -/
theorem main_mean_actual_zero_Th (M : ABKModel 2) (m : ℤ) :
    mainMeanActual_Th M m 0 = (nativeCompletedSourceMean M m 5).toReal := by
  exact in_source_mean_old_endpoint M m 5

/-- The exact fifth source row gives the initial mean envelope in the actual
cutoff law. The premise is the depth-five coordinate of the corrected
`NA-SOURCE-ROWS` contract, before any outward-rounded corollary. -/
theorem main_mean_actual_initial_cap_Th (M : ABKModel 2) (m : ℤ)
    (hrows : NativeSourceRowsBounds M m)
    (hγ : M.gamma ≤ gammaZero) :
    mainMeanActual_Th M m 0 ≤ theta M * mainSourceMeanPrefix := by
  have hMean5 : nativeCompletedSourceMean M m 5 ≤
      ENNReal.ofReal (theta M * (inSourceA5 : ℝ)) := by
    simpa [inSourceA5] using NativeSourceRowsBounds.mean_five hrows
  rw [main_mean_actual_zero_Th]
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hMean5
  have hθ : theta M ≤ 1 := ASDExplicitGamma.Cold.cold_theta_le_one M hγ
  have hθ0 : 0 ≤ theta M := by
    unfold theta
    exact div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have hsource : (inSourceA5 : ℝ) = mainSourceMeanPrefix := by
    norm_num [inSourceA5, mainSourceMeanPrefix, observer1Panel0Data]
  have hcap : 0 ≤ (inSourceA5 : ℝ) := by
    norm_num [inSourceA5]
  rw [ENNReal.toReal_ofReal (mul_nonneg hθ0 hcap)] at hreal
  calc
    (nativeCompletedSourceMean M m 5).toReal ≤
        theta M * (inSourceA5 : ℝ) := hreal
    _ = theta M * mainSourceMeanPrefix := by rw [hsource]

end ASDExplicitGamma.Main
