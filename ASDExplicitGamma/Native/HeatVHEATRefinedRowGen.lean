module

public import ASDExplicitGamma.Native.HeatVHEATRefinedRow
public import ASDExplicitGamma.Native.HeatVHEATSourceCarrierGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedShellLawGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceClocksGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedSourceProfilesGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedSourceTransportGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceGeometryGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceBankGen
public import ASDExplicitGamma.Native.HeatVHEATDriftBankIdentityGen
public import ASDExplicitGamma.Native.HeatVHEATDriftBankMeasurableGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceIntegrandGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceNormsGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceExpectationGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedCoefficientsGen
public import ASDExplicitGamma.Native.HeatVHEATDriftConfiguredCoefficientsGen
public import ASDExplicitGamma.Native.HeatVHEATDriftConfiguredExpectationGen
public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedProfileGen
public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedExpectationGen
public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedPhysicalGen
public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedBindingGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedSourceObserverGen
public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedActualGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedAssemblyGen

/-! The `ns`-shell generalization of `HeatVHEATRefinedRow`. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open ProbabilityTheory

variable (ns : ℕ) [NeZero ns]

/-- Any Gaussian-series realization of the actual refined carrier band has
the same covariance after an arbitrary bounded carrier-to-child map as the
sum of the nine selected physical shell covariances. In particular, choosing
the centered child remainder map gives the shellwise covariance bridge used
by the VHEAT bracket estimate. -/
theorem nativeHeatQ3RefinedCarrierCovariance_eq_sum_actualShellRows_of_law_Gen
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ)
    (Ffam : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m ns)
    {T : BandHilbert ns →L[ℝ] C(nativeHeatQ3RefinedCarrierDomain m, ℝ)}
    {v : ℕ → BandHilbert ns}
    (hA : Summable (fun j => ‖v j‖ ^ 2))
    (hlaw : (Cutoff.cutoffSampleLaw M).toMeasure.map
        (modelBand (nativeHeatQ3RefinedCarrierDomain m)
          (nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns)) =
      standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T))
    (A : C(nativeHeatQ3RefinedCarrierDomain m, ℝ) →L[ℝ]
      (∀ i : nativeHeatQ3RefinedCarrierIndex,
        C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ)))
    {Φ : (∀ i : nativeHeatQ3RefinedCarrierIndex,
        C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ)) → ℝ}
    (hΦ : HasPolynomiallyBoundedC2Derivatives Φ)
    (x : ∀ i : nativeHeatQ3RefinedCarrierIndex,
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ)) :
    modelCovarianceTrace Φ (fun j => A (T (v j))) x =
      ∑ i : Fin ns, modelCovarianceTrace Φ
        (fun j => A ((Ffam).factor i
          ((Ffam).direction i j))) x := by
  classical
  let V : Fin ns → Type := fun _ => GaussianFactorL2 ℕ
  let S := nativeHeatQ3RefinedCarrierFreshShellSeriesFactorGen Ffam
  let w := nativeHeatQ3RefinedCarrierFreshShellSeriesDirectionsGen Ffam
  let hB := nativeHeatQ3RefinedCarrierFreshShellSeriesSummableGen Ffam
  have hlawSource := nativeHeatQ3RefinedCarrierFreshShellSeriesLawGen Ffam
  have hseriesLaw : standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T) =
      standardGaussianInfinitePi.map (gaussianSeriesLimitE hB S) :=
    hlaw.symm.trans hlawSource
  have hmapLaw : (standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T)).map A =
      (standardGaussianInfinitePi.map (gaussianSeriesLimitE hB S)).map A := by
    rw [hseriesLaw]
  have hmapLaw' : standardGaussianInfinitePi.map (gaussianSeriesLimitE hA (A.comp T)) =
      standardGaussianInfinitePi.map (gaussianSeriesLimitE hB (A.comp S)) := by
    have hh := hmapLaw
    rw [Measure.map_map A.continuous.measurable
          (stronglyMeasurable_gaussianSeriesLimitE hA T).measurable,
        Measure.map_map A.continuous.measurable
          (stronglyMeasurable_gaussianSeriesLimitE hB S).measurable] at hh
    exact hh
  have htrace := modelCovarianceTrace_eq_of_law hA (A.comp T) hB (A.comp S)
    hmapLaw' hΦ x
  have htrace' : modelCovarianceTrace Φ (fun j => A (T (v j))) x =
      modelCovarianceTrace Φ (fun j => A (S (w j))) x := by
    simpa only [ContinuousLinearMap.comp_apply] using htrace
  have hBsum : Summable (fun j => ‖A (S (w j))‖ ^ 2) :=
    summable_sq_bounded_image _ hB (A.comp S)
  have hBi (i : Fin ns) : Summable (fun j =>
      ‖A (Ffam.factor i (Ffam.direction i j))‖ ^ 2) :=
    summable_sq_bounded_image _ (Ffam.squareSummable i) (A.comp (Ffam.factor i))
  have hcov := modelCovarianceTrace_eq_bilinearTraceMap
    (fun j => A (S (w j))) hBsum hΦ.1 x
  have hcov_i (i : Fin ns) := modelCovarianceTrace_eq_bilinearTraceMap
    (fun j => A (Ffam.factor i (Ffam.direction i j))) (hBi i) hΦ.1 x
  have hcomp : A.comp S = finiteFactor V (fun i => A.comp (Ffam.factor i)) := by
    ext z
    simp [S, V, nativeHeatQ3RefinedCarrierFreshShellSeriesFactorGen,
      finiteFactor]
  have hmap : (fun j => A (S (w j))) =
      (fun j => finiteFactor V (fun i => A.comp (Ffam.factor i))
        (finiteDirections V Ffam.direction j)) := by
    funext j
    have hh := congrArg (fun L => L (finiteDirections V Ffam.direction j)) hcomp
    simpa [S, w, V,
      nativeHeatQ3RefinedCarrierFreshShellSeriesFactorGen,
      nativeHeatQ3RefinedCarrierFreshShellSeriesDirectionsGen,
      nativeHeatQ3RefinedCarrierFreshShellFamily] using hh
  have hmap_point j := congrFun hmap j
  calc
    modelCovarianceTrace Φ (fun j => A (T (v j))) x =
        modelCovarianceTrace Φ (fun j => A (S (w j))) x := htrace'
    _ = bilinearTraceMap (fun j => A (S (w j))) hBsum
        (fderiv ℝ (fderiv ℝ Φ) x) := hcov
    _ = ∑ i : Fin ns, bilinearTraceMap
        (fun j => A (Ffam.factor i (Ffam.direction i j))) (hBi i)
        (fderiv ℝ (fderiv ℝ Φ) x) := by
          simp only [bilinearTraceMap_apply]
          change (∑' j, (fderiv ℝ (fderiv ℝ Φ) x) (A (S (w j))) (A (S (w j)))) = _
          simp_rw [hmap_point]
          simpa [V, finiteFactor_bilinearTrace_eq_sum_refined,
            ContinuousLinearMap.comp_apply] using
            (finiteFactor_bilinearTrace_eq_sum_refined Ffam.direction Ffam.squareSummable
              (fun i => A.comp (Ffam.factor i)) (fderiv ℝ (fderiv ℝ Φ) x))
    _ = ∑ i : Fin ns, modelCovarianceTrace Φ
        (fun j => A (Ffam.factor i (Ffam.direction i j))) x := by
          apply Finset.sum_congr rfl
          intro i hi
          exact (hcov_i i).symm
