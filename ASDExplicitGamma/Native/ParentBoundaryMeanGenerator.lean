module

public import ASDExplicitGamma.Native.ParentBoundaryMeanGeometry
public import ASDExplicitGamma.Native.ParentBoundaryMeanObserverBank
public import ASDExplicitGamma.Native.ParentBoundaryMeanBankProducts

/-! Actual full physical mean heat generators on the parent source cells. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Model Triadic Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- The literal full uncentered physical shell mean generator, in the
unchanged starting true frame. -/
def parentBoundaryMeanShellGenerator (M : ABKModel 2) (h : ℝ) (q n : ℤ)
    (height : ℕ) (t : ℝ) (i : Fin height) (ω : Cutoff.CutoffSample 2) : ℝ :=
  (1/2:ℝ)*modelCovarianceTrace (modelTraceObservable q M.nu (Annealed.sigmaBar M n))
    (pureFluxMainCubeQ3Directions q (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ)))
      (q3ModelLength (n+((i.val+1:ℕ):ℤ)))) (parentBoundaryObserverBandScalar q n height t ω)

/-- Every actual full mean shell generator is Bochner integrable, before
any numerical estimate is inserted. -/
theorem parent_boundary_mean_shell_generator_integrable
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (q n : ℤ)
    (height : ℕ) (hheight : 1 ≤ height) (t : ℝ) (i : Fin height) :
    Integrable (parentBoundaryMeanShellGenerator M h q n height t i) (Cutoff.cutoffSampleLaw M).toMeasure := by
  have hΦ := modelTraceObservable_hasPolynomiallyBoundedC2Derivatives q M.nu (Annealed.sigmaBar M n)
    M.nu_pos (Annealed.sigmaBar_characterization M n).1
  have htest := source_q3_covariance_trace_regular q
    (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))) (q3ModelLength (n+((i.val+1:ℕ):ℤ))) _ hΦ
  have hm := parent_boundary_observer_band_test_memLp M h hM q n height hheight _ htest.1 htest.2 t 2 (by norm_num)
  exact (hm.integrable (by norm_num : (1:ℝ≥0∞) ≤ ENNReal.ofReal (2:ℝ))).const_mul _

end
end ASDExplicitGamma.Native
