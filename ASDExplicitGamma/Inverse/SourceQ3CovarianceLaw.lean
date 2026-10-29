module

public import ASDExplicitGamma.Inverse.RawShellQ3Law

/-! Actual-shell covariance contraction for the source mean (before the
real-power chain rule). Adapted from RawShellQ3Law's law-identification proof. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 Homogenization
open scoped ENNReal

theorem source_q3_test_covariance_trace_eq_of_fresh_law
    (n : ℤ) (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (s : ℕ)
    (T : GaussianFactorL2 ℕ →L[ℝ]
      C(closure (cubeSet (originCube 2 n)), ℝ))
    (v : ℕ → GaussianFactorL2 ℕ) (hA : Summable (fun j => ‖v j‖ ^ 2)
    )
    (hlaw : (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω : Cutoff.CutoffSample 2 => shellFieldScalarRestriction
        (closure (cubeSet (originCube 2 n))) (ω.1 (n + (s : ℤ)))) =
      standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T))
    (Φ : C(closure (cubeSet (originCube 2 n)), ℝ) → ℝ)
    (hΦ : HasPolynomiallyBoundedC2Derivatives Φ)
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    modelCovarianceTrace Φ (fun j => T (v j)) x =
      modelCovarianceTrace Φ
        (pureFluxMainCubeQ3Directions n
          (q3ModelAmplitude M h (n + (s : ℤ)))
          (q3ModelLength (n + (s : ℤ)))) x := by
  classical
  let m := n + (s : ℤ) - 1
  let b := q3ModelAmplitude M h (n + (s : ℤ))
  let L := q3ModelLength (n + (s : ℤ))
  let K := closure (cubeSet (originCube 2 n))
  have htime : m + 1 = n + (s : ℤ) := by dsimp [m]; omega
  have hactual : (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω : Cutoff.CutoffSample 2 => shellFieldScalarRestriction K (ω.1 (m + 1))) =
      standardGaussianInfinitePi.map (mainCubeQ3Series n b L) := by
    simpa [m, b, L] using main_actual_fresh_cube_factor_law n M h hM m
  have hcanonical : standardGaussianInfinitePi.map (mainCubeQ3Series n b L) =
      standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T) :=
    hactual.symm.trans (by simpa [K, htime] using hlaw)
  have htrace := @modelCovarianceTrace_eq_of_law
    (GaussianFactorL2 ℕ) (MainCubeH3 n b L)
    (C(closure (cubeSet (originCube 2 n)), ℝ))
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance (mainCubeH3InnerProductSpace n b L) inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    v hA T (mainCubeQ3Directions n b L) (mainCubeQ3Directions_summable n b L)
    (mainCubeH3Value n b L) hcanonical.symm Φ hΦ x
  exact htrace

theorem source_q3_covariance_trace_eq_of_fresh_law
    (n : ℤ) (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (s : ℕ) (σ : ℝ) (hσ : 0 < σ)
    (T : GaussianFactorL2 ℕ →L[ℝ]
      C(closure (cubeSet (originCube 2 n)), ℝ))
    (v : ℕ → GaussianFactorL2 ℕ) (hA : Summable (fun j => ‖v j‖ ^ 2)
    )
    (hlaw : (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω : Cutoff.CutoffSample 2 => shellFieldScalarRestriction
        (closure (cubeSet (originCube 2 n))) (ω.1 (n + (s : ℤ)))) =
      standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T))
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    let Φ := modelTraceObservable n M.nu σ
    modelCovarianceTrace Φ (fun j => T (v j)) x =
      modelCovarianceTrace Φ
        (pureFluxMainCubeQ3Directions n
          (q3ModelAmplitude M h (n + (s : ℤ)))
          (q3ModelLength (n + (s : ℤ)))) x := by
  classical
  let m := n + (s : ℤ) - 1
  let b := q3ModelAmplitude M h (n + (s : ℤ))
  let L := q3ModelLength (n + (s : ℤ))
  let K := closure (cubeSet (originCube 2 n))
  let Φ := modelTraceObservable n M.nu σ
  have htime : m + 1 = n + (s : ℤ) := by dsimp [m]; omega
  have hΦ : HasPolynomiallyBoundedC2Derivatives Φ :=
    modelTraceObservable_hasPolynomiallyBoundedC2Derivatives n M.nu σ M.nu_pos hσ
  have hactual : (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω : Cutoff.CutoffSample 2 => shellFieldScalarRestriction K (ω.1 (m + 1))) =
      standardGaussianInfinitePi.map (mainCubeQ3Series n b L) := by
    simpa [m, b, L] using main_actual_fresh_cube_factor_law n M h hM m
  have hcanonical : standardGaussianInfinitePi.map (mainCubeQ3Series n b L) =
      standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T) :=
    hactual.symm.trans (by simpa [K, htime] using hlaw)
  have htrace := @modelCovarianceTrace_eq_of_law
    (GaussianFactorL2 ℕ) (MainCubeH3 n b L)
    (C(closure (cubeSet (originCube 2 n)), ℝ))
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance (mainCubeH3InnerProductSpace n b L) inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    v hA T (mainCubeQ3Directions n b L) (mainCubeQ3Directions_summable n b L)
    (mainCubeH3Value n b L) hcanonical.symm Φ hΦ x
  exact htrace

end ASDExplicitGamma.Inverse
