module

public import ASDExplicitGamma.Native.ParentBoundaryWeakMeanTheta
public import ASDExplicitGamma.Native.ParentBoundaryWeakGeometric
public import ASDExplicitGamma.Native.ParentBoundaryCommonDepthTheta
public import ASDExplicitGamma.Native.ParentBoundaryMeanSourceReturn
public import ASDExplicitGamma.Native.ParentBoundaryBandHistoryStationarity
public import ASDExplicitGamma.Native.OldSignedInitialWeightedMean

/-! The actual complete parent weak-history return, with original rare reserve. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Model Triadic Cold Algsuperdiff.Section3
noncomputable section

/-- The literal expected descendant mean at every weak depth has the
proved physical heat return, with its exact completed initial coordinate. -/
theorem parent_boundary_weak_cell_mean_return
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (n : ℤ) (height : ℕ) (hheight : 1 ≤ height)
    (hpast : ∀ k<n,nativeInductionState M h k) (hstate : nativeInductionState M h n)
    (depth : ℕ) (hdepth : depth=5) (U : TriadicCube 2) (hU : U∈descendantsAtDepth (originCube 2 n) depth)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (j : ℕ) :
    (∫ ω,parentBoundaryBandCellTrace M n height t U j ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      (∫ ω,cutoffTraceDefect M n (n-((5+j:ℕ):ℤ)) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)+
        t*parentBoundaryMeanDepthSlope M.gamma height j := by
  have hstation := parent_boundary_band_trace_mean_depth M h hM n height hheight depth U hU t j
  have hq : n-(depth:ℤ)-(j:ℤ)=n-((5+j:ℕ):ℤ) := by omega
  have hh := parent_boundary_mean_depth_return M h hM hg n j height hheight hpast hstate t ht0 ht1
  have he : (nativeCompletedSourceMean M n (5+j)).toReal=
      ∫ ω,cutoffTraceDefect M n (n-((5+j:ℕ):ℤ)) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
    symm
    exact integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (cutoffTraceDefect_nonneg M n (n-((5+j:ℕ):ℤ))))
      (cutoffTraceDefect_measurable M n (n-((5+j:ℕ):ℤ))).aestronglyMeasurable
  have hobserver : (∫ ω,parentBoundaryBandCellTrace M n height t U j ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)=
      parentBoundaryObserverBandAverage M (n-((5+j:ℕ):ℤ)) n height
        (modelTraceObservable (n-((5+j:ℕ):ℤ)) M.nu (Annealed.sigmaBar M n)) t := by
    calc
      _ = _ := hstation
      _ = _ := by
        rw [hq]
        unfold parentBoundaryObserverBandAverage
        apply integral_congr_ae
        filter_upwards [] with ω
        exact (parent_boundary_observer_band_trace_eq M (n-((5+j:ℕ):ℤ)) n height t ω).symm
  exact (le_of_eq hobserver).trans (hh.trans_eq (congrArg
    (fun x : ℝ => x+t*parentBoundaryMeanDepthSlope M.gamma height j) he))

end
end ASDExplicitGamma.Native
