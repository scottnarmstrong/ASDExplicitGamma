module

public import ASDExplicitGamma.Native.ParentBoundaryMeanTheta
public import ASDExplicitGamma.Native.ParentBoundaryMeanDepthSlope
public import ASDExplicitGamma.Native.SmallerGamma
public import ASDExplicitGamma.Numerics.Native.SetupParent001
public import ASDExplicitGamma.Numerics.Native.SetupParent002
public import ASDExplicitGamma.Numerics.Native.SetupParent003
public import ASDExplicitGamma.Numerics.Native.SetupParent004
public import ASDExplicitGamma.Numerics.Native.SetupParent005
public import ASDExplicitGamma.Numerics.Native.SetupParent006
public import ASDExplicitGamma.Numerics.Native.SetupParent007
public import ASDExplicitGamma.Numerics.Native.SetupParent008
public import ASDExplicitGamma.Numerics.Native.SetupParent009
public import ASDExplicitGamma.Numerics.Native.SetupParent010
public import ASDExplicitGamma.Numerics.Native.SetupParent011
public import ASDExplicitGamma.Numerics.Native.SetupParent012
public import ASDExplicitGamma.Numerics.Native.SetupParent013
public import ASDExplicitGamma.Numerics.Native.SetupParent014
public import ASDExplicitGamma.Numerics.Native.SetupParent015
public import ASDExplicitGamma.Numerics.Native.SetupParent016
public import ASDExplicitGamma.Native.GenericSourceUnconditionalRows

/-! Actual initial source coordinates and physical mean return at every weak depth. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Model Triadic Cold Algsuperdiff.Section3 Numerics.Native Set
noncomputable section

/-- The physical observation-square trace at time zero is literally the
completed cutoff trace with the original starting frame. -/
theorem parent_boundary_mean_observer_initial_trace
    (M : ABKModel 2) (q n : ℤ) (height : ℕ) (ω : Cutoff.CutoffSample 2) :
    modelTraceObservable q M.nu (Annealed.sigmaBar M n)
      (parentBoundaryObserverBandScalar q n height 0 ω)=cutoffTraceDefect M n q ω := by
  rw [parent_boundary_observer_band_trace_eq,parent_boundary_common_band_coefficient_zero]
  rfl

/-- Exact initial actual mean at arbitrary observation depth. -/
theorem parent_boundary_mean_observer_initial
    (M : ABKModel 2) (n : ℤ) (r height : ℕ) :
    parentBoundaryObserverBandAverage M (n-(r:ℤ)) n height
      (modelTraceObservable (n-(r:ℤ)) M.nu (Annealed.sigmaBar M n)) 0=
      (nativeCompletedSourceMean M n r).toReal := by
  unfold parentBoundaryObserverBandAverage
  simp_rw [parent_boundary_mean_observer_initial_trace]
  exact integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (cutoffTraceDefect_nonneg M n (n-(r:ℤ))))
    (cutoffTraceDefect_measurable M n (n-(r:ℤ))).aestronglyMeasurable

/-- The ACTUAL mean at depth5+j has its full finite-band return from the
literal completed initial mean, without any assumed source estimate. -/
theorem parent_boundary_mean_depth_return
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (n : ℤ) (j height : ℕ) (hheight : 1 ≤ height)
    (hpast : ∀ k<n,nativeInductionState M h k) (hstate : nativeInductionState M h n)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    parentBoundaryObserverBandAverage M (n-((5+j:ℕ):ℤ)) n height
      (modelTraceObservable (n-((5+j:ℕ):ℤ)) M.nu (Annealed.sigmaBar M n)) t ≤
      (nativeCompletedSourceMean M n (5+j)).toReal+t*parentBoundaryMeanDepthSlope M.gamma height j := by
  let q := n-((5+j:ℕ):ℤ)
  let F := parentBoundaryObserverBandAverage M q n height
    (modelTraceObservable q M.nu (Annealed.sigmaBar M n))
  have hheat := parent_boundary_mean_observer_heat M h hM q n (by dsimp [q]; omega) height hheight
  have hh := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le ht0
    (show ContinuousOn F (Icc 0 t) from hheat.1.mono (fun _ hx => hx.1))
    (fun s hs => (hheat.2 s hs.1).hasDerivWithinAt)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le ht0).mp
      (intervalIntegrable_const : IntervalIntegrable
        (fun _ : ℝ => parentBoundaryMeanDepthSlope M.gamma height j) volume 0 t))
    (fun s hs => parent_boundary_mean_depth_generator_slope M h hM hg q n j rfl
      height hheight hpast hstate s (hs.2.le.trans ht1))
  simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul] at hh
  have hzero : F 0=(nativeCompletedSourceMean M n (5+j)).toReal :=
    parent_boundary_mean_observer_initial M n (5+j) height
  change F t ≤ _
  rw [←hzero]
  linarith only [hh]

end
end ASDExplicitGamma.Native
