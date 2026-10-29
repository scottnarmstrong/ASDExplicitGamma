module

public import ASDExplicitGamma.Native.GenericSourceBandPowerHeat

/-! Initial coordinates for the simultaneous actual source-band heat path. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Variational
open scoped ENNReal
noncomputable section

/-- The simultaneous source mean starts at the literal frozen ordinary mean. -/
theorem native_source_band_mean_zero (M : ABKModel 2) (n : ℤ) (height : ℕ) :
    nativeSourceBandMean M n height 0=(ordinaryMean M n).toReal := by
  unfold nativeSourceBandMean nativeSourceBandScalar
  simp only [Real.sqrt_zero,zero_smul,add_zero]
  simp_rw [native_source_model_trace_older_eq]
  exact integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (cutoffTraceDefect_nonneg M n n))
    (cutoffTraceDefect_measurable M n n).aestronglyMeasurable

/-- The native starting state supplies the initial ordinary-mean coordinate
for the simultaneous source ODE, before any framing or refinement. -/
theorem native_source_band_mean_zero_le
    (M : ABKModel 2) (h : ℝ) (n : ℤ) (height : ℕ)
    (hstate : nativeInductionState M h n) :
    nativeSourceBandMean M n height 0 ≤ (3/50:ℝ)*theta M := by
  rw [native_source_band_mean_zero]
  have htheta : 0 ≤ theta M := by
    unfold theta
    exact div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hstate.1).trans_eq
    (ENNReal.toReal_ofReal (mul_nonneg (by norm_num) htheta))

/-- At time zero the simultaneous twentieth root is the completed source
root, including the same fixed true frame and unmodified coefficient law. -/
theorem native_source_band_p20_root_zero (M : ABKModel 2) (n : ℤ) (height : ℕ) :
    nativeSourceBandAverage M n height
      (fun x => modelTraceObservable n M.nu (Annealed.sigmaBar M n) x^(20:ℝ)) 0^((20:ℝ)⁻¹) =
      nativeSourceBandRoot M n 0 := by
  unfold nativeSourceBandAverage nativeSourceBandScalar nativeSourceBandRoot
  simp only [Real.sqrt_zero,zero_smul,add_zero,Nat.cast_zero]

end
end ASDExplicitGamma.Native
