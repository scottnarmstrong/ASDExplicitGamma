module

public import ASDExplicitGamma.Gaussian.CovarianceTrace
public import ASDExplicitGamma.Gaussian.FiniteFactorLaw
public import ASDExplicitGamma.Gaussian.BasisIndependence
public import ASDExplicitGamma.Gaussian.ModelHeatPower
public import ASDExplicitGamma.Native.HeatVHEATRefinedCarrier
public import ASDExplicitGamma.Native.HeatVHEATRefinedShellLaw

/-! Exact assembly of the refined depth-ten carrier generator into its nine
actual fresh-shell rows. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open ProbabilityTheory

/-- Bilinear covariance traces split over the exact finite direct-sum basis
used by the heterogeneous shell realization. -/
theorem finiteFactor_bilinearTrace_eq_sum_refined
    {b : ℕ} [NeZero b] {V : Fin b → Type*}
    [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ∀ i, ℕ → V i)
    (hv : ∀ i, Summable (fun j => ‖v i j‖ ^ 2))
    (T : ∀ i, V i →L[ℝ] E)
    (B : E →L[ℝ] E →L[ℝ] ℝ) :
    ∑' j, B (finiteFactor V T (finiteDirections V v j))
        (finiteFactor V T (finiteDirections V v j)) =
      ∑ i, ∑' j, B (T i (v i j)) (T i (v i j)) := by
  classical
  have hs (i : Fin b) : Summable (fun j => B (T i (v i j)) (T i (v i j))) :=
    summable_bilinear_images (hv i) B (T i) (T i)
  have hp : Summable (fun p : Fin b × ℕ =>
      B (T p.1 (v p.1 p.2)) (T p.1 (v p.1 p.2))) := by
    apply Summable.of_norm
    rw [summable_prod_of_nonneg (fun p => norm_nonneg
      (B (T p.1 (v p.1 p.2)) (T p.1 (v p.1 p.2)) ))]
    exact ⟨fun i => (hs i).norm, Summable.of_finite⟩
  simp only [finiteDirections, finiteFactor_single]
  rw [(bandIndex b).tsum_eq
      (fun p : Fin b × ℕ => B (T p.1 (v p.1 p.2)) (T p.1 (v p.1 p.2))),
    hp.tsum_prod' hs]
  exact tsum_fintype _

/-- Any Gaussian-series realization of the actual refined carrier band has
the same covariance after an arbitrary bounded carrier-to-child map as the
sum of the nine selected physical shell covariances. In particular, choosing
the centered child remainder map gives the shellwise covariance bridge used
by the VHEAT bracket estimate. -/
theorem nativeHeatQ3RefinedCarrierCovariance_eq_sum_actualShellRows_of_law
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ)
    {T : BandHilbert 9 →L[ℝ] C(nativeHeatQ3RefinedCarrierDomain m, ℝ)}
    {v : ℕ → BandHilbert 9}
    (hA : Summable (fun j => ‖v j‖ ^ 2))
    (hlaw : (Cutoff.cutoffSampleLaw M).toMeasure.map
        (modelBand (nativeHeatQ3RefinedCarrierDomain m)
          (nativeHeatQ3RefinedCarrierPhysicalShells m)) =
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
      ∑ i : Fin 9, modelCovarianceTrace Φ
        (fun j => A ((nativeHeatQ3RefinedCarrierFreshShellFamily M h hM m).factor i
          ((nativeHeatQ3RefinedCarrierFreshShellFamily M h hM m).direction i j))) x := by
  classical
  let V : Fin 9 → Type := fun _ => GaussianFactorL2 ℕ
  let F := nativeHeatQ3RefinedCarrierFreshShellFamily M h hM m
  let S := nativeHeatQ3RefinedCarrierFreshShellSeriesFactor M h hM m
  let w := nativeHeatQ3RefinedCarrierFreshShellSeriesDirections M h hM m
  let hB := nativeHeatQ3RefinedCarrierFreshShellSeriesSummable M h hM m
  have hlawSource := nativeHeatQ3RefinedCarrierFreshShellSeriesLaw M h hM m
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
  have hBi (i : Fin 9) : Summable (fun j =>
      ‖A (F.factor i (F.direction i j))‖ ^ 2) :=
    summable_sq_bounded_image _ (F.squareSummable i) (A.comp (F.factor i))
  have hcov := modelCovarianceTrace_eq_bilinearTraceMap
    (fun j => A (S (w j))) hBsum hΦ.1 x
  have hcov_i (i : Fin 9) := modelCovarianceTrace_eq_bilinearTraceMap
    (fun j => A (F.factor i (F.direction i j))) (hBi i) hΦ.1 x
  have hcomp : A.comp S = finiteFactor V (fun i => A.comp (F.factor i)) := by
    ext z
    simp [S, F, V, nativeHeatQ3RefinedCarrierFreshShellSeriesFactor,
      nativeHeatQ3RefinedCarrierFreshShellFamily, finiteFactor]
  have hmap : (fun j => A (S (w j))) =
      (fun j => finiteFactor V (fun i => A.comp (F.factor i))
        (finiteDirections V F.direction j)) := by
    funext j
    have hh := congrArg (fun L => L (finiteDirections V F.direction j)) hcomp
    simpa [S, w, F, V,
      nativeHeatQ3RefinedCarrierFreshShellSeriesFactor,
      nativeHeatQ3RefinedCarrierFreshShellSeriesDirections,
      nativeHeatQ3RefinedCarrierFreshShellFamily] using hh
  have hmap_point j := congrFun hmap j
  calc
    modelCovarianceTrace Φ (fun j => A (T (v j))) x =
        modelCovarianceTrace Φ (fun j => A (S (w j))) x := htrace'
    _ = bilinearTraceMap (fun j => A (S (w j))) hBsum
        (fderiv ℝ (fderiv ℝ Φ) x) := hcov
    _ = ∑ i : Fin 9, bilinearTraceMap
        (fun j => A (F.factor i (F.direction i j))) (hBi i)
        (fderiv ℝ (fderiv ℝ Φ) x) := by
          simp only [bilinearTraceMap_apply]
          change (∑' j, (fderiv ℝ (fderiv ℝ Φ) x) (A (S (w j))) (A (S (w j)))) = _
          simp_rw [hmap_point]
          simpa [F, V, finiteFactor_bilinearTrace_eq_sum_refined,
            ContinuousLinearMap.comp_apply] using
            (finiteFactor_bilinearTrace_eq_sum_refined F.direction F.squareSummable
              (fun i => A.comp (F.factor i)) (fderiv ℝ (fderiv ℝ Φ) x))
    _ = ∑ i : Fin 9, modelCovarianceTrace Φ
        (fun j => A (F.factor i (F.direction i j))) x := by
          apply Finset.sum_congr rfl
          intro i hi
          exact (hcov_i i).symm

end ASDExplicitGamma.Native

end
