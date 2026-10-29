module

public import ASDExplicitGamma.Native.OldSignedQ1HeatReturn
public import ASDExplicitGamma.Native.SourceSmallerGammaInterface

/-! The completed q1 boundary charge from the actual OLD signed generator. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Main Triadic Cold Variational Algsuperdiff.Section3 Numerics.Native
noncomputable section

/-- NA-Q1-BOUNDARY-CHARGE: the actual completed source mean has the exact
certified cap. Only the source model and strict previous native states occur
as premises; no q1, panel, generator, bank or inverse estimate is assumed. -/
theorem native_completed_q1_bound
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ k < m,nativeInductionState M h k) :
    nativeCompletedSourceMean M m 1 ≤ ENNReal.ofReal (theta M*(nativeBoundaryQ1Sharp:ℝ)) := by
  rw [nativeCompletedSourceMean,←ofReal_integral_eq_lintegral_ofReal
    (integrable_cutoffTraceDefect M m (m-(1:ℕ)))
    (Filter.Eventually.of_forall (cutoffTraceDefect_nonneg M m (m-(1:ℕ))))]
  apply ENNReal.ofReal_le_ofReal
  have hh := old_signed_q1_completed_mean_return M h hM hg (m-1)
    (fun k hk => hpast k (by omega))
  have he : (nativeEndpointQ1001Cap:ℝ)=(nativeBoundaryQ1Sharp:ℝ) := by
    norm_num [nativeEndpointQ1001Cap,nativeBoundaryQ1Sharp]
  simpa only [sub_add_cancel,Nat.cast_one,he] using hh

/-- The same q1 proof supplies the real-valued carried Q-star input of the
refined source rows at every completed cutoff. -/
theorem native_completed_q1_integral_carried
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ k < m,nativeInductionState M h k) :
    (∫ ω,cutoffTraceDefect M m (m-1) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      theta M*(nativeQstar:ℝ) := by
  have hh := old_signed_q1_completed_mean_return M h hM hg (m-1)
    (fun k hk => hpast k (by omega))
  simp only [sub_add_cancel] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    (Rat.cast_le.mpr (nativeEndpointQ1001_carried.1.trans nativeEndpointQ1001_carried.2).le)
      (cold_theta_pos M).le)

end
end ASDExplicitGamma.Native
