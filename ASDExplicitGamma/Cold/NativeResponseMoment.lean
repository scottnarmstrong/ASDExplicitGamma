module

public import ASDExplicitGamma.Cold.NativeResponseLaw
public import ASDExplicitGamma.Cold.OldGraphGlobal
public import ASDExplicitGamma.Cold.RawInterpolation
public import ASDExplicitGamma.Cold.NativeMomentSystem
public import ASDExplicitGamma.Cold.SpectralVarianceCharge

/-! # Genuine native response variance caps from strictly earlier scalar means -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Matrix Algsuperdiff.Section3
open scoped ENNReal
namespace ASDExplicitGamma.Cold
open ASDExplicitGamma.Numerics.Cold

/-- Native raw trace L2 caps follow from the actual moment hierarchy and the checked certificate. -/
theorem cold_native_raw_interpolation (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ)
    {θ : ℝ} (hθ : 0 ≤ θ) (hroot : root20 M m ≤ ENNReal.ofReal (θ*(coldR20:ℝ)))
    {n k : ℕ} (_hn : n ≤ 128) (hk : k < n) (hk126 : k ≤ 126)
    (hmean : ∀ i < n, coldNativeMean M m i ≤ θ*(coldMeanAt i:ℝ)) :
    lpNorm (coldNativeTrace M m k) 2 (Cutoff.cutoffSampleLaw M).toMeasure ≤ θ*(coldInterpolationAt k:ℝ) :=
  cold_raw_interpolation_table_cap hθ hk126 (coldNativeTrace_memLp hroot k)
    (Filter.Eventually.of_forall (coldNativeTrace_nonneg M m k)) (hmean k hk)
    (cold_native_moment_table M h hM m hθ hroot (by omega) (fun i hi => hmean i (hi.trans hk)))

/-- The actual centered full response variance is bounded by its raw spectral charge. -/
theorem coldNativeResponse_center_cap (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    {D L : ℝ} (hT : MemLp (coldNativeCellTrace M m Q) 2 (Cutoff.cutoffSampleLaw M).toMeasure)
    (hmean : (∫ ω, coldNativeCellTrace M m Q ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ D)
    (hcap : lpNorm (coldNativeCellTrace M m Q) 2 (Cutoff.cutoffSampleLaw M).toMeasure ≤ L) :
    matrixFrobeniusL2 (Cutoff.cutoffSampleLaw M).toMeasure
      (fun ω => coldNativeResponse M m Q ω-matrixMean (Cutoff.cutoffSampleLaw M).toMeasure (coldNativeResponse M m Q)) ≤
        Real.sqrt (2*D+L^2) :=
  matrix_center_l2_le_of_spectral _ _ (coldNativeResponse_memLp_of_trace M m Q hT) hT
    (coldNativeResponse_spectral M m Q) hmean hcap

end ASDExplicitGamma.Cold
