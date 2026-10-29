module

public import ASDExplicitGamma.Gaussian.SeriesLawVariance
public import ASDExplicitGamma.Native.HeatVHEATSourceCarrier

/-! The source-normalized auxiliary center Gaussian, whose covariance is
`(1 + θ) * (1 - t)` times the covariance of the actual center vector. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization ASDExplicitGamma.Gaussian
open Algsuperdiff.Section3 ProbabilityTheory
open scoped ENNReal NNReal Topology

/-- The scalar observation of the selected refined-band Gaussian series at
one actual child center, with the source's inflated auxiliary variance. -/
noncomputable def nativeHeatQ3RefinedCarrierSourceAuxCenterObservation
    (M : ABKModel 2) (m : ℤ) (θ t : ℝ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    C(nativeHeatQ3RefinedCarrierDomain m, ℝ) →L[ℝ] ℝ :=
  (Real.sqrt ((1 + θ) * (1 - t)) /
      (Annealed.sigmaBar M (m + 1) : ℝ)) •
    ContinuousMap.evalCLM ℝ (nativeHeatQ3RefinedCarrierCenter m i)

/-- The exact scalar variance of the source auxiliary center coordinate. -/
noncomputable def nativeHeatQ3RefinedCarrierSourceAuxCenterVariance
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (θ t : ℝ) (i : nativeHeatQ3RefinedCarrierIndex) : ℝ≥0 :=
  Real.toNNReal (∑' j,
    (nativeHeatQ3RefinedCarrierSourceAuxCenterObservation M m θ t i
      (nativeHeatQ3RefinedCarrierFreshShellSeriesFactor M h hM m
        (nativeHeatQ3RefinedCarrierFreshShellSeriesDirections M h hM m j))) ^ 2)

/-- The source auxiliary scalar coordinate, in the physical coefficient
units used by the translated source trace. -/
noncomputable def nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (θ t : ℝ) (i : nativeHeatQ3RefinedCarrierIndex)
    (ξ : ℕ → ℝ) : ℝ :=
  (Annealed.sigmaBar M (m + 1) : ℝ) *
    nativeHeatQ3RefinedCarrierSourceAuxCenterObservation M m θ t i
      (gaussianSeriesLimitE
        (nativeHeatQ3RefinedCarrierFreshShellSeriesSummable M h hM m)
        (nativeHeatQ3RefinedCarrierFreshShellSeriesFactor M h hM m) ξ)

/-- The source auxiliary coordinate is exactly the source-scaled value of
the selected fresh-band field at the child's center. -/
theorem nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian_eq_centerValue
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (θ t : ℝ) (i : nativeHeatQ3RefinedCarrierIndex)
    (ξ : ℕ → ℝ) :
    nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian M h hM m θ t i ξ =
      Real.sqrt ((1 + θ) * (1 - t)) *
        gaussianSeriesLimitE
          (nativeHeatQ3RefinedCarrierFreshShellSeriesSummable M h hM m)
          (nativeHeatQ3RefinedCarrierFreshShellSeriesFactor M h hM m) ξ
          (nativeHeatQ3RefinedCarrierCenter m i) := by
  have hσ : (Annealed.sigmaBar M (m + 1) : ℝ) ≠ 0 :=
    ne_of_gt (Annealed.sigmaBar_characterization M (m + 1)).1
  change (Annealed.sigmaBar M (m + 1) : ℝ) *
      ((Real.sqrt ((1 + θ) * (1 - t)) /
        (Annealed.sigmaBar M (m + 1) : ℝ)) * _ ) = _
  field_simp [hσ]
  simp

/-- The source auxiliary vector is exactly the unscaled center-map input to
the backward test at heat variance `(1 + θ) * (1 - t)`. -/
theorem nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian_eq_backwardCenterInput
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (θ t : ℝ) (i : nativeHeatQ3RefinedCarrierIndex)
    (ξ : ℕ → ℝ) :
    nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian M h hM m θ t i ξ =
      Real.sqrt ((1 + θ) * (1 - t)) *
        nativeHeatQ3RefinedCarrierSourceCenterMap m
          (gaussianSeriesLimitE
            (nativeHeatQ3RefinedCarrierFreshShellSeriesSummable M h hM m)
            (nativeHeatQ3RefinedCarrierFreshShellSeriesFactor M h hM m) ξ) i := by
  rw [nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian_eq_centerValue]
  rfl

/-- These source auxiliary coordinates are measurable functions of the one
common standard Gaussian sequence, preserving all correlations. -/
theorem nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian_measurable
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (θ t : ℝ) (i : nativeHeatQ3RefinedCarrierIndex) :
    Measurable
      (nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian M h hM m θ t i) := by
  let hA := nativeHeatQ3RefinedCarrierFreshShellSeriesSummable M h hM m
  let T := nativeHeatQ3RefinedCarrierFreshShellSeriesFactor M h hM m
  let A := nativeHeatQ3RefinedCarrierSourceAuxCenterObservation M m θ t i
  have hZ : StronglyMeasurable (gaussianSeriesLimitE hA T) :=
    stronglyMeasurable_gaussianSeriesLimitE hA T
  change Measurable (fun ξ =>
    (Annealed.sigmaBar M (m + 1) : ℝ) * A (gaussianSeriesLimitE hA T ξ))
  exact measurable_const.mul (A.continuous.measurable.comp hZ.measurable)

/-- Each source auxiliary center coordinate has its exact marginal Gaussian
law after normalization by the true frame scale. -/
theorem nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian_law
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (θ t : ℝ) (i : nativeHeatQ3RefinedCarrierIndex) :
    standardGaussianInfinitePi.map
      (fun ξ => nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian
          M h hM m θ t i ξ /
        (Annealed.sigmaBar M (m + 1) : ℝ)) =
      gaussianReal 0
        (nativeHeatQ3RefinedCarrierSourceAuxCenterVariance M h hM m θ t i) := by
  let hA := nativeHeatQ3RefinedCarrierFreshShellSeriesSummable M h hM m
  let T := nativeHeatQ3RefinedCarrierFreshShellSeriesFactor M h hM m
  let A := nativeHeatQ3RefinedCarrierSourceAuxCenterObservation M m θ t i
  let w := nativeHeatQ3RefinedCarrierFreshShellSeriesDirections M h hM m
  have hσ : (Annealed.sigmaBar M (m + 1) : ℝ) ≠ 0 :=
    ne_of_gt (Annealed.sigmaBar_characterization M (m + 1)).1
  have hpoint :
      (fun ξ => nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian
          M h hM m θ t i ξ /
        (Annealed.sigmaBar M (m + 1) : ℝ)) =
      fun ξ => A (gaussianSeriesLimitE hA T ξ) := by
    funext ξ
    change ((Annealed.sigmaBar M (m + 1) : ℝ) *
        A (gaussianSeriesLimitE hA T ξ)) /
        (Annealed.sigmaBar M (m + 1) : ℝ) = _
    field_simp [hσ]
  rw [hpoint]
  simpa [nativeHeatQ3RefinedCarrierSourceAuxCenterVariance, A, hA, T, w] using
    (map_gaussianSeriesLimitE_linear hA T A)

end ASDExplicitGamma.Native
