module

public import ASDExplicitGamma.Native.ParentBoundaryMeanSlope
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Actual physical parent mean heat transport with all source estimates discharged. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Model Triadic Algsuperdiff.Section3 Set
noncomputable section

/-- Exact physical mean heat identity on the observation square, with the
finite covariance sum integrated term by term. -/
theorem parent_boundary_mean_observer_heat
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (q n : ℤ) (hqn : q ≤ n) (height : ℕ) (hheight : 1 ≤ height) :
    let F := parentBoundaryObserverBandAverage M q n height
      (modelTraceObservable q M.nu (Annealed.sigmaBar M n))
    ContinuousOn F (Ici 0) ∧ ∀ t ∈ Ioi (0:ℝ), HasDerivAt F
      (∑ i : Fin height, ∫ ω, parentBoundaryMeanShellGenerator M h q n height t i ω
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) t := by
  intro F
  have hΦ := modelTraceObservable_hasPolynomiallyBoundedC2Derivatives q M.nu
    (Annealed.sigmaBar M n) M.nu_pos (Annealed.sigmaBar_characterization M n).1
  have hh := parent_boundary_observer_band_average_shell_heat M h hM q n hqn height hheight _ hΦ
  refine ⟨hh.1,?_⟩
  intro t ht
  have hd := hh.2 t ht
  have he : (1/2:ℝ)*(∫ ω : Cutoff.CutoffSample 2, ∑ i : Fin height,
      modelCovarianceTrace (modelTraceObservable q M.nu (Annealed.sigmaBar M n))
        (pureFluxMainCubeQ3Directions q (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ)))
          (q3ModelLength (n+((i.val+1:ℕ):ℤ)))) (parentBoundaryObserverBandScalar q n height t ω)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      ∑ i : Fin height, ∫ ω, parentBoundaryMeanShellGenerator M h q n height t i ω
        ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
    rw [←integral_const_mul]
    calc
      _ = ∫ ω, ∑ i : Fin height,parentBoundaryMeanShellGenerator M h q n height t i ω
          ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
        apply integral_congr_ae
        filter_upwards [] with ω
        exact Finset.mul_sum _ _ _
      _ = _ := integral_finsetSum _ (fun i _ =>
        parent_boundary_mean_shell_generator_integrable M h hM q n height hheight t i)
  rw [he] at hd
  exact hd

end
end ASDExplicitGamma.Native
