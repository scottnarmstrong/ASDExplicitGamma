module

public import ASDExplicitGamma.Inverse.RawShellQ3PowerGenerator
public import ASDExplicitGamma.Gaussian.ModelHeatTrace
public import ASDExplicitGamma.Gaussian.BilinearCovariance
public import ASDExplicitGamma.Gaussian.BasisIndependence
public import ASDExplicitGamma.Main.CubeFactor
public import ASDExplicitGamma.Main.Q3HeatIdentity

/-! The actual inserted-shell heat realization and the canonical q3 H3
realization give the same p=20 generator at every coefficient. -/

@[expose] public section

namespace ASDExplicitGamma.Inverse

open MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 Homogenization
open scoped ENNReal

/-- The covariance and carré-du-champ terms in the actual trace heat generator
are unchanged when the fresh shell's actual Gaussian realization is replaced
by the canonical q3 H3 factor. -/
theorem raw_trace_model_q3_power_generator_eq_of_fresh_law
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
    modelPowerHeatGenerator Φ (fun j => T (v j)) 20 x =
      modelPowerHeatGenerator Φ
        (pureFluxMainCubeQ3Directions n
          (q3ModelAmplitude M h (n + (s : ℤ)))
          (q3ModelLength (n + (s : ℤ)))) 20 x := by
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
  let d := fderiv ℝ Φ x
  let Bform : C(closure (cubeSet (originCube 2 n)), ℝ) →L[ℝ]
      C(closure (cubeSet (originCube 2 n)), ℝ) →L[ℝ] ℝ := d.smulRight d
  have hgradTrace := @bilinearTrace_eq_of_law
    (GaussianFactorL2 ℕ) (MainCubeH3 n b L)
    (C(closure (cubeSet (originCube 2 n)), ℝ))
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance (mainCubeH3InnerProductSpace n b L) inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    v hA T (mainCubeQ3Directions n b L) (mainCubeQ3Directions_summable n b L)
    (mainCubeH3Value n b L) hcanonical.symm Bform
  have hgrad : modelGradientSquareTrace Φ (fun j => T (v j)) x =
      modelGradientSquareTrace Φ (pureFluxMainCubeQ3Directions n b L) x := by
    change (∑' j, d (T (v j)) ^ 2) =
      ∑' j, d (mainCubeH3Value n b L (mainCubeQ3Directions n b L j)) ^ 2
    convert hgradTrace using 1 <;>
      simp [Bform, ContinuousLinearMap.smulRight_apply, smul_eq_mul, pow_two] <;> rfl
  change modelPowerHeatGenerator Φ (fun j => T (v j)) 20 x =
    modelPowerHeatGenerator Φ (pureFluxMainCubeQ3Directions n b L) 20 x
  unfold modelPowerHeatGenerator
  rw [htrace, hgrad]
  rfl

end ASDExplicitGamma.Inverse
