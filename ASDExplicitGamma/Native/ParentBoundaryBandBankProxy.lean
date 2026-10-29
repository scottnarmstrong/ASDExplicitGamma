module

public import ASDExplicitGamma.Native.ParentBoundaryBandWeak
public import ASDExplicitGamma.Native.ParentBoundaryBrokenInverse
public import ASDExplicitGamma.Native.GenericSourceBandHistory

/-! Actual simultaneous-band weak proxy paid by the SAME complete local
bank and shifted physical weak-trace history, with constant 1+alpha. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 Response Scalar Gaussian Main Triadic Variational Inverse
noncomputable section

/-- The complete actual source proxy is controlled by one local bank
majorant. All cell histories and infinite-series convergence are discharged
from the model/native states; no inverse-history estimate is a premise. -/
theorem parent_boundary_actual_band_bank_proxy
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ) (height depth : ℕ) (hdepth : depth≤5)
    (hpast : ∀ l<n,nativeInductionState M h l) (t : ℝ) (ht : t≤1) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      parentBoundaryBandWeakProxy M n height depth t omega≤
        (1+inverseHistoryDiscount)*(nativeSourceBandHistory M n height t omega).toReal*
          rawWeakTraceHistory (fun j => parentBoundaryBandTraceDepth M n height t omega (depth+j)) := by
  have hb := native_source_band_local_bank M h hM hg n height hpast t ht
  filter_upwards [hb.history_finite] with omega hfinite
  let Q := originCube 2 n
  let a := parentBoundaryBandFrameField M n height t omega
  let P := (nativeSourceBandHistory M n height t omega).toReal
  have hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
    M.nu (Annealed.sigmaBar M n) M.nu_pos (Annealed.sigmaBar_characterization M n).1
    (pureFluxOpenResponseRestriction n (nativeSourceBandScalar n height t omega))
  have hP (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
      lemmaVInverseHistory U a ((3:ℝ)^(1/4:ℝ))≤P :=
    native_source_band_mesh_history_le M n height t omega depth hdepth hfinite.ne hU
  have hd (j : ℕ) : inverseHistoryDiscount^j*
      parentBoundaryBandInverseDepth M n height t omega (depth+j)≤P := by
    rw [parent_boundary_band_inverse_depth]
    exact parent_boundary_broken_inverse_discount Q depth a hEll P hP j
  have hT (j : ℕ) : 0≤parentBoundaryBandTraceDepth M n height t omega (depth+j) := by
    rw [←parent_boundary_band_trace_depth]
    apply descendantsAverage_nonneg
    intro U hU
    exact Cold.coarse_square_traceDefect_nonneg U
      (hEll.mono (measurableSet_openCubeSet U) (openCubeSet_subset_of_mem_descendantsAtDepth hU))
  have hsProxy := (parent_boundary_actual_band_weak_budget M n height depth t omega).2.2
  have hsTrace : Summable (fun j : ℕ => inverseHistoryDiscount^j*
      parentBoundaryBandTraceDepth M n height t omega (depth+j)) := by
    have hs := parent_boundary_broken_weak_trace_summable Q depth a hEll
    apply hs.congr
    intro j
    rw [parent_boundary_band_trace_depth]
  exact raw_weak_trace_proxy_le _ _ P hd hT hsProxy hsTrace

end
end ASDExplicitGamma.Native
