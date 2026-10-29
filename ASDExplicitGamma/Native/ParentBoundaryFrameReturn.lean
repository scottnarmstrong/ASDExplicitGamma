module

public import ASDExplicitGamma.Native.GenericSourceBandEndpoint
public import ASDExplicitGamma.Native.SourceSmallerGammaInterface
public import ASDExplicitGamma.Cold.NativeTrace

/-! Exact true-frame restoration of the actual own-native band endpoint.
The structural exponential is retained before numerical rounding. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 Response Scalar Gaussian Main Triadic Variational Inverse
noncomputable section

/-- The actual completed source mean is bounded by the actual time-one
simultaneous-band mean times its exact structural frame factor. There is
no endpoint estimate premise and no frame assigned to an intermediate law. -/
theorem parent_boundary_completed_mean_frame (M : ABKModel 2) (n : ℤ) (height : ℕ) :
    nativeCompletedSourceMean M (n+(height:ℤ)) height≤
      ENNReal.ofReal ((3:ℝ)^(2*M.gamma*(height:ℝ))*nativeSourceBandMean M n height 1) := by
  have hs := (Annealed.sigmaBar_characterization M n).1
  have hratio := ASDExplicitGamma.Scalar.sigmaBar_structural_continuity_nat M n height
  have hb := main_completed_frame_return_of_ratio M (n+(height:ℤ)) n
    (Annealed.sigmaBar M n) ((3:ℝ)^(2*M.gamma*(height:ℝ))) hs hratio.1 hratio.2
  rw [←native_source_band_mean_one,main_completed_trace_integral_eq] at hb
  have he : nativeCompletedSourceMean M (n+(height:ℤ)) height=
      ENNReal.ofReal (∫ omega,cutoffTraceDefect M (n+(height:ℤ)) n omega
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) := by
    unfold nativeCompletedSourceMean
    rw [show n+(height:ℤ)-(height:ℤ)=n by omega]
    exact (ofReal_integral_eq_lintegral_ofReal
      (ASDExplicitGamma.Cold.integrable_cutoffTraceDefect M (n+(height:ℤ)) n)
      (Filter.Eventually.of_forall (cutoffTraceDefect_nonneg M (n+(height:ℤ)) n))).symm
  rw [he]
  exact ENNReal.ofReal_le_ofReal hb

end
end ASDExplicitGamma.Native
