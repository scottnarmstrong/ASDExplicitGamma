module

public import ASDExplicitGamma.Native.GenericSourceBandProfile
public import ASDExplicitGamma.Inverse.FullResponseCoefficientTransport
public import ASDExplicitGamma.Main.FrameEndpoint

/-! Literal completed coefficient endpoint and true-frame source mean. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic ASDExplicitGamma.Variational ASDExplicitGamma.Response
noncomputable section

/-- Time one contains the entire terminal cutoff on the source cube. -/
theorem native_source_band_trace_one (M : ABKModel 2) (n : ℤ) (height : ℕ)
    (ω : Cutoff.CutoffSample 2) :
    modelTraceObservable n M.nu (Annealed.sigmaBar M n) (nativeSourceBandScalar n height 1 ω)=
      traceDefect (cubeSet (originCube 2 n))
        (Cutoff.coefficientCutoff M.nu (n+(height:ℤ)) ω).toFun (Annealed.sigmaBar M n) := by
  have hae : responsePlanarCoefficientField M.nu
      (ContinuousMap.linearIsometryBoundedOfCompact (closure (cubeSet (originCube 2 n))) ℝ ℝ
        (nativeSourceBandScalar n height 1 ω)) =ᵐ[volume.restrict (cubeSet (originCube 2 n))]
      (Cutoff.coefficientCutoff M.nu (n+(height:ℤ)) ω).toFun := by
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_cubeSet (originCube 2 n))] with x hx
    have hh := native_source_band_coefficient_on_cube M n height 1 ω x hx
    simpa only [Real.sqrt_one,full_response_coefficient_unit M n (n+(height:ℤ)) (by omega) ω] using hh
  unfold modelTraceObservable traceDefect
  rw [coarseBlockMatrix_congr_of_ae_eq hae]

/-- The simultaneous endpoint mean equals its literal coefficient-law mean,
without truncating or changing the fixed starting frame. -/
theorem native_source_band_mean_one (M : ABKModel 2) (n : ℤ) (height : ℕ) :
    nativeSourceBandMean M n height 1 =
      ∫ a : RegCoeffField 2, traceDefect (cubeSet (originCube 2 n)) a.toFun
        (Annealed.sigmaBar M n) ∂(Cutoff.coefficientCutoffLaw M (n+(height:ℤ))) := by
  rw [ASDExplicitGamma.Main.main_completed_trace_integral_eq]
  exact integral_congr_ae (Filter.Eventually.of_forall (native_source_band_trace_one M n height))

/-- Structural continuity restores the completed true frame after all fresh
shells have been inserted; the mean uses the completed-law frame map. -/
theorem native_source_band_completed_mean_frame
    (M : ABKModel 2) (n : ℤ) (height : ℕ) (hg : M.gamma ≤ gammaZero) (hh : height ≤ 1332) :
    (∫ ω, cutoffTraceDefect M (n+(height:ℤ)) n ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      nativeSourceE M.gamma height*nativeSourceBandMean M n height 1 := by
  have hratio := ASDExplicitGamma.Scalar.sigmaBar_structural_continuity_nat M n height
  have hE := native_source_E_ge_three_power M.gamma height M.shellPrefix.gamma_pos.le hg (by omega)
  have hR : (Annealed.sigmaBar M (n+(height:ℤ)):ℝ)/(Annealed.sigmaBar M n:ℝ) ≤
      nativeSourceE M.gamma height :=
    hratio.2.trans (by
      convert hE using 1
      congr 1
      ring)
  rw [native_source_band_mean_one]
  change (∫ ω, traceDefect (cubeSet (originCube 2 n))
    (Cutoff.coefficientCutoff M.nu (n+(height:ℤ)) ω).toFun
      (Annealed.sigmaBar M (n+(height:ℤ)):ℝ) ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ _
  rw [←ASDExplicitGamma.Main.main_completed_trace_integral_eq]
  exact ASDExplicitGamma.Main.main_completed_frame_return_of_ratio M (n+(height:ℤ)) n
    (Annealed.sigmaBar M n) (nativeSourceE M.gamma height)
    (Annealed.sigmaBar_characterization M n).1 hratio.1 hR

/-- The actual completed source mean obeys the literal finite generic
mean producer, with full128, all four p20 passes, rare terms and framing. -/
theorem native_source_completed_generic_mean
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hpast : ∀ j < n, nativeInductionState M h j)
    (hstate : nativeInductionState M h n) (height : ℕ) (hheight : 1 ≤ height) (hh : height ≤ 1332) :
    (∫ ω, cutoffTraceDefect M (n+(height:ℤ)) n ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      nativeSourceGenericMean M.gamma height ((3/50:ℝ)*theta M) (3/10^46:ℝ)
        (nativeSourceGenericIndividualProfile M.gamma (theta M) height)
        (nativeSourceGenericVarianceCap M.gamma height) := by
  have hbound := native_source_band_mean_rational_solution M h hM hg n hpast hstate height hheight hh
  exact (native_source_band_completed_mean_frame M n height hg hh).trans
    (mul_le_mul_of_nonneg_left hbound
      (native_source_E_nonneg M.gamma height M.shellPrefix.gamma_pos.le hg (by omega)))

end
end ASDExplicitGamma.Native
