module

public import ASDExplicitGamma.Native.ParentBoundaryObserverBandCoefficient
public import ASDExplicitGamma.Native.ParentBoundaryObserverBandMoments
public import ASDExplicitGamma.Native.ParentBoundaryBandFull64
public import ASDExplicitGamma.Inverse.SourceQ3TraceRegularity
public import ASDExplicitGamma.Inverse.SourceQ3PowerIdentity
public import ASDExplicitGamma.Inverse.FullResponseTrace

/-! Literal observer-square band traces, their full64 bank, and honest
integrability of each physical shell power generator. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- The actual observer heat trace is the physical fixed-frame band defect. -/
theorem parent_boundary_observer_band_trace_eq (M : ABKModel 2) (q n : ℤ)
    (height : ℕ) (t : ℝ) (omega : Cutoff.CutoffSample 2) :
    modelTraceObservable q M.nu (Annealed.sigmaBar M n)
      (parentBoundaryObserverBandScalar q n height t omega)=
      traceDefect (cubeSet (originCube 2 q))
        (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) omega) (Annealed.sigmaBar M n) := by
  have hae : responsePlanarCoefficientField M.nu
      (ContinuousMap.linearIsometryBoundedOfCompact (closure (cubeSet (originCube 2 q))) ℝ ℝ
        (parentBoundaryObserverBandScalar q n height t omega)) =ᵐ[volume.restrict (cubeSet (originCube 2 q))]
      attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) omega := by
    filter_upwards [ae_restrict_mem (measurableSet_cubeSet (originCube 2 q))] with x hx
    exact parent_boundary_observer_band_coefficient_on_cube M q n height t omega x hx
  unfold modelTraceObservable traceDefect
  rw [coarseBlockMatrix_congr_of_ae_eq hae]

/-- The actual observer full trace is exactly the closed full-response bank test. -/
theorem parent_boundary_observer_band_full_trace_eq (M : ABKModel 2) (q n : ℤ)
    (height : ℕ) (t : ℝ) (omega : Cutoff.CutoffSample 2) :
    modelTraceObservable q M.nu (Annealed.sigmaBar M n)
      (parentBoundaryObserverBandScalar q n height t omega)+4=
      nativeSourceFullResponseTrace M (originCube 2 q) n (n+(height:ℤ)) (fun _ => Real.sqrt t) omega := by
  rw [parent_boundary_observer_band_trace_eq,traceDefect_eq_full_framedTrace]
  unfold nativeSourceFullResponseTrace
  ring

end
end ASDExplicitGamma.Native
