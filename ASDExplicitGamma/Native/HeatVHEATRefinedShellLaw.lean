module

public import ASDExplicitGamma.Gaussian.FiniteFactorLaw
public import ASDExplicitGamma.Native.HeatVHEATRefinedCarrier
public import ASDExplicitGamma.Native.HeatVHEATFamily
public import ASDExplicitGamma.Native.HeatVHEATShellTranslation

/-! The actual fresh-shell Gaussian-series family and its restriction laws on
the refined depth-ten VHEAT carrier. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open ProbabilityTheory

/-- A chosen Gaussian-series realization of the nine actual refined shells. -/
structure NativeHeatQ3RefinedCarrierFreshShellFamily
    (M : ABKModel 2) (K : Set (Vec 2)) [CompactSpace K]
    (bands : Fin 9 → ℤ) where
  factor : Fin 9 → GaussianFactorL2 ℕ →L[ℝ] C(K, ℝ)
  direction : Fin 9 → ℕ → GaussianFactorL2 ℕ
  squareSummable : ∀ i, Summable (fun j => ‖direction i j‖ ^ 2)
  law : ∀ i, (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω : Cutoff.CutoffSample 2 =>
        shellFieldScalarRestriction K (ω.1 (bands i))) =
    standardGaussianInfinitePi.map
      (gaussianSeriesLimitE (squareSummable i) (factor i))

/-- Choose a Gaussian-series factor for each of the nine physical refined
shells on the common carrier. -/
noncomputable def nativeHeatQ3RefinedCarrierFreshShellFamily
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ) :
    NativeHeatQ3RefinedCarrierFreshShellFamily M
      (nativeHeatQ3RefinedCarrierDomain m)
      (nativeHeatQ3RefinedCarrierPhysicalShells m) := by
  classical
  have hshell (i : Fin 9) :=
    freshShell_map_scalarRestriction_eq_gaussianSeries M h hM
      (nativeHeatQ3RefinedCarrierPhysicalShells m i - 1)
      (K := nativeHeatQ3RefinedCarrierDomain m)
  choose factor direction squareSummable law using hshell
  refine ⟨factor, direction, squareSummable, ?_⟩
  intro i
  simpa only [Int.sub_add_cancel] using law i

/-- The direct-sum factor for the nine selected refined-shell factors. -/
noncomputable def nativeHeatQ3RefinedCarrierFreshShellSeriesFactor
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ) :
    BandHilbert 9 →L[ℝ] C(nativeHeatQ3RefinedCarrierDomain m, ℝ) :=
  finiteFactor (fun _ : Fin 9 => GaussianFactorL2 ℕ)
    (fun i => (nativeHeatQ3RefinedCarrierFreshShellFamily M h hM m).factor i)

/-- The direct-sum directions for the nine selected refined-shell factors. -/
noncomputable def nativeHeatQ3RefinedCarrierFreshShellSeriesDirections
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ) :
    ℕ → BandHilbert 9 :=
  finiteDirections (fun _ : Fin 9 => GaussianFactorL2 ℕ)
    (fun i => (nativeHeatQ3RefinedCarrierFreshShellFamily M h hM m).direction i)

/-- Square summability of the refined nine-shell direct-sum directions. -/
theorem nativeHeatQ3RefinedCarrierFreshShellSeriesSummable
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ) :
    Summable (fun j =>
      ‖nativeHeatQ3RefinedCarrierFreshShellSeriesDirections M h hM m j‖ ^ 2) := by
  exact finiteDirections_summable
    (fun _ : Fin 9 => GaussianFactorL2 ℕ)
    (fun i => (nativeHeatQ3RefinedCarrierFreshShellFamily M h hM m).direction i)
    (fun i => (nativeHeatQ3RefinedCarrierFreshShellFamily M h hM m).squareSummable i)

/-- The actual refined carrier band has the Gaussian-series law of the
explicit direct-sum factor and directions. -/
theorem nativeHeatQ3RefinedCarrierFreshShellSeriesLaw
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ) :
    (Cutoff.cutoffSampleLaw M).toMeasure.map
        (modelBand (nativeHeatQ3RefinedCarrierDomain m)
          (nativeHeatQ3RefinedCarrierPhysicalShells m)) =
      standardGaussianInfinitePi.map
        (gaussianSeriesLimitE
          (nativeHeatQ3RefinedCarrierFreshShellSeriesSummable M h hM m)
          (nativeHeatQ3RefinedCarrierFreshShellSeriesFactor M h hM m)) := by
  classical
  let K := nativeHeatQ3RefinedCarrierDomain m
  let bands := nativeHeatQ3RefinedCarrierPhysicalShells m
  have hbands : Function.Injective bands :=
    nativeHeatQ3RefinedCarrierPhysicalShells_injective m
  let F := nativeHeatQ3RefinedCarrierFreshShellFamily M h hM m
  simpa [K, bands, F, nativeHeatQ3RefinedCarrierFreshShellSeriesFactor,
    nativeHeatQ3RefinedCarrierFreshShellSeriesDirections,
    nativeHeatQ3RefinedCarrierFreshShellSeriesSummable] using
    (modelBand_law_of_factors
      (fun _ : Fin 9 => GaussianFactorL2 ℕ) K M bands hbands
      F.factor F.direction F.squareSummable F.law)

private theorem map_gaussianSeriesLimitE_continuousMap_refined
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [SecondCountableTopology V] [MeasurableSpace V]
    [BorelSpace V] [OpensMeasurableSpace V]
    {K L : Set (Vec 2)} [CompactSpace K] [SecondCountableTopology K]
    [LocallyCompactSpace K] [CompactSpace L] [SecondCountableTopology L]
    [LocallyCompactSpace L] (v : ℕ → V)
    (hv : Summable (fun j => ‖v j‖ ^ 2))
    (T : V →L[ℝ] C(K, ℝ)) (A : C(K, ℝ) →L[ℝ] C(L, ℝ)) :
    (standardGaussianInfinitePi.map (gaussianSeriesLimitE hv T)).map A =
      standardGaussianInfinitePi.map
        (gaussianSeriesLimitE hv (A.comp T)) := by
  apply measure_eq_of_continuousMap_eval_linearCombination
  intro ι _ x t
  let Lsum : C(L, ℝ) →L[ℝ] ℝ :=
    ∑ j, t j • ContinuousMap.evalCLM ℝ (x j)
  have hLsum (f : C(L, ℝ)) :
      continuousMapEvalLinearCombination ι x t f = Lsum f := by
    simp [Lsum, continuousMapEvalLinearCombination,
      ContinuousMap.evalCLM_apply, smul_eq_mul]
  have hcomboMeas : Measurable (continuousMapEvalLinearCombination ι x t) := by
    change Measurable (fun f : C(L, ℝ) => ∑ j, t j * f (x j))
    exact Finset.measurable_sum Finset.univ fun j hj =>
      measurable_const.mul (ContinuousMap.measurable_eval (x j))
  have hseriesMeas := (stronglyMeasurable_gaussianSeriesLimitE hv T).measurable
  have hseriesCompMeas :=
    (stronglyMeasurable_gaussianSeriesLimitE hv (A.comp T)).measurable
  have hleft :
      ((standardGaussianInfinitePi.map (gaussianSeriesLimitE hv T)).map A).map
          (continuousMapEvalLinearCombination ι x t) =
        gaussianReal 0 (Real.toNNReal
          (∑' j, (Lsum (A (T (v j)))) ^ 2)) := by
    calc
      _ = standardGaussianInfinitePi.map
          (fun ω => Lsum (A (gaussianSeriesLimitE hv T ω))) := by
            rw [Measure.map_map hcomboMeas A.continuous.measurable,
              Measure.map_map
                (hcomboMeas.comp A.continuous.measurable) hseriesMeas]
            congr 1
            funext ω
            exact hLsum (A (gaussianSeriesLimitE hv T ω))
      _ = _ := map_gaussianSeriesLimitE_linear hv T (Lsum.comp A)
  have hright :
      (standardGaussianInfinitePi.map
        (gaussianSeriesLimitE hv (A.comp T))).map
          (continuousMapEvalLinearCombination ι x t) =
        gaussianReal 0 (Real.toNNReal
          (∑' j, (Lsum (A (T (v j)))) ^ 2)) := by
    calc
      _ = standardGaussianInfinitePi.map
          (fun ω => Lsum (gaussianSeriesLimitE hv (A.comp T) ω)) := by
            rw [Measure.map_map hcomboMeas hseriesCompMeas]
            congr 1
            funext ω
            exact hLsum (gaussianSeriesLimitE hv (A.comp T) ω)
      _ = _ := map_gaussianSeriesLimitE_linear hv (A.comp T) Lsum
  rw [hleft, hright]

/-- Restricting the selected refined-shell factor to a child closure gives
the law of that child's actual physical shell. -/
theorem nativeHeatQ3RefinedCarrierChildFreshShellLaw
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (i : nativeHeatQ3RefinedCarrierIndex) (d : Fin 9) :
    let F := nativeHeatQ3RefinedCarrierFreshShellFamily M h hM m
    let P := (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun j : nativeHeatQ3RefinedCarrierIndex =>
        C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m j)), ℝ)) i).comp
      (nativeHeatQ3RefinedCarrierOldMap m)
    let T := P.comp (F.factor d)
    (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω : Cutoff.CutoffSample 2 =>
        shellFieldScalarRestriction
          (closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)))
          (ω.1 (nativeHeatQ3RefinedCarrierPhysicalShells m d))) =
      standardGaussianInfinitePi.map
        (gaussianSeriesLimitE (F.squareSummable d) T) := by
  classical
  let K := nativeHeatQ3RefinedCarrierDomain m
  let U := closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i))
  let F := nativeHeatQ3RefinedCarrierFreshShellFamily M h hM m
  let P : C(K, ℝ) →L[ℝ] C(U, ℝ) :=
    (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun j : nativeHeatQ3RefinedCarrierIndex =>
        C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m j)), ℝ)) i).comp
      (nativeHeatQ3RefinedCarrierOldMap m)
  let T := P.comp (F.factor d)
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have hsample : Measurable (fun ω : Cutoff.CutoffSample 2 =>
      shellFieldScalarRestriction K
        (ω.1 (nativeHeatQ3RefinedCarrierPhysicalShells m d))) :=
    (measurable_shellFieldScalarRestriction K).comp
      ((measurable_pi_apply (nativeHeatQ3RefinedCarrierPhysicalShells m d)).comp
        measurable_subtype_coe)
  have hrestriction : (fun ω : Cutoff.CutoffSample 2 =>
      P (shellFieldScalarRestriction K
        (ω.1 (nativeHeatQ3RefinedCarrierPhysicalShells m d)))) =
      (fun ω : Cutoff.CutoffSample 2 =>
        shellFieldScalarRestriction U
          (ω.1 (nativeHeatQ3RefinedCarrierPhysicalShells m d))) := by
    funext ω
    apply ContinuousMap.ext
    intro x
    simp [P, K, U, nativeHeatQ3RefinedCarrierOldMap,
      ContinuousMap.compCLM_apply]
    rfl
  have hseriesMap : Measure.map P
      (standardGaussianInfinitePi.map
        (gaussianSeriesLimitE (F.squareSummable d) (F.factor d))) =
      standardGaussianInfinitePi.map (gaussianSeriesLimitE
        (F.squareSummable d) (P.comp (F.factor d))) := by
    exact map_gaussianSeriesLimitE_continuousMap_refined
      (F.direction d) (F.squareSummable d) (F.factor d) P
  calc
    μ.map (fun ω : Cutoff.CutoffSample 2 =>
        shellFieldScalarRestriction U
          (ω.1 (nativeHeatQ3RefinedCarrierPhysicalShells m d))) =
      μ.map (fun ω : Cutoff.CutoffSample 2 =>
        P (shellFieldScalarRestriction K
          (ω.1 (nativeHeatQ3RefinedCarrierPhysicalShells m d)))) := by
            rw [hrestriction]
    _ = Measure.map P (μ.map (fun ω : Cutoff.CutoffSample 2 =>
        shellFieldScalarRestriction K
          (ω.1 (nativeHeatQ3RefinedCarrierPhysicalShells m d)))) := by
            exact (Measure.map_map P.continuous.measurable hsample).symm
    _ = Measure.map P
        (standardGaussianInfinitePi.map
          (gaussianSeriesLimitE (F.squareSummable d) (F.factor d))) := by
            rw [F.law d]
    _ = standardGaussianInfinitePi.map
        (gaussianSeriesLimitE (F.squareSummable d) T) := by
            simpa [T] using hseriesMap

/-- The selected shell factor, pulled back from a refined child to its
origin cube, has the origin-cube physical shell law. -/
theorem nativeHeatQ3RefinedCarrierChildFreshShellOriginLaw
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (i : nativeHeatQ3RefinedCarrierIndex) (d : Fin 9) :
    let F := nativeHeatQ3RefinedCarrierFreshShellFamily M h hM m
    let P := (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun j : nativeHeatQ3RefinedCarrierIndex =>
        C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m j)), ℝ)) i).comp
      (nativeHeatQ3RefinedCarrierOldMap m)
    let A := nativeHeat_translateTriadicFieldToOrigin
      (nativeHeatQ3RefinedCarrierChild m i)
    (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω : Cutoff.CutoffSample 2 =>
        shellFieldScalarRestriction
          (closure (cubeSet (originCube 2
            (nativeHeatQ3RefinedCarrierChild m i).scale)))
          (ω.1 (nativeHeatQ3RefinedCarrierPhysicalShells m d))) =
      standardGaussianInfinitePi.map
        (gaussianSeriesLimitE (F.squareSummable d)
          (A.comp (P.comp (F.factor d)))) := by
  classical
  let Q := nativeHeatQ3RefinedCarrierChild m i
  let U := closure (cubeSet Q)
  let U0 := closure (cubeSet (originCube 2 Q.scale))
  let F := nativeHeatQ3RefinedCarrierFreshShellFamily M h hM m
  let P : C(nativeHeatQ3RefinedCarrierDomain m, ℝ) →L[ℝ] C(U, ℝ) :=
    (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun j : nativeHeatQ3RefinedCarrierIndex =>
        C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m j)), ℝ)) i).comp
      (nativeHeatQ3RefinedCarrierOldMap m)
  let A : C(U, ℝ) →L[ℝ] C(U0, ℝ) :=
    nativeHeat_translateTriadicFieldToOrigin Q
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have hsample : Measurable (fun ω : Cutoff.CutoffSample 2 =>
      shellFieldScalarRestriction U
        (ω.1 (nativeHeatQ3RefinedCarrierPhysicalShells m d))) :=
    (measurable_shellFieldScalarRestriction U).comp
      ((measurable_pi_apply (nativeHeatQ3RefinedCarrierPhysicalShells m d)).comp
        measurable_subtype_coe)
  have hchild : μ.map (fun ω : Cutoff.CutoffSample 2 =>
      shellFieldScalarRestriction U
        (ω.1 (nativeHeatQ3RefinedCarrierPhysicalShells m d))) =
      standardGaussianInfinitePi.map (gaussianSeriesLimitE
        (F.squareSummable d) (P.comp (F.factor d))) := by
    simpa [F, P, Q, U] using
      (nativeHeatQ3RefinedCarrierChildFreshShellLaw M h hM m i d)
  have htranslate :=
    nativeHeat_shellRestrictionLaw_translateTriadicCube_toOrigin
      M (nativeHeatQ3RefinedCarrierPhysicalShells m d) Q
  have hseries := map_gaussianSeriesLimitE_continuousMap_refined
    (F.direction d) (F.squareSummable d) (P.comp (F.factor d)) A
  calc
    μ.map (fun ω : Cutoff.CutoffSample 2 =>
        shellFieldScalarRestriction U0
          (ω.1 (nativeHeatQ3RefinedCarrierPhysicalShells m d))) =
      μ.map (fun ω : Cutoff.CutoffSample 2 => A
        (shellFieldScalarRestriction U
          (ω.1 (nativeHeatQ3RefinedCarrierPhysicalShells m d)))) := by
            simpa [Q, U, U0, A] using htranslate.symm
    _ = (μ.map (fun ω : Cutoff.CutoffSample 2 =>
        shellFieldScalarRestriction U
          (ω.1 (nativeHeatQ3RefinedCarrierPhysicalShells m d)))).map A := by
            exact (Measure.map_map A.continuous.measurable hsample).symm
    _ = (standardGaussianInfinitePi.map (gaussianSeriesLimitE
        (F.squareSummable d) (P.comp (F.factor d)))).map A := by
            rw [hchild]
    _ = standardGaussianInfinitePi.map
        (gaussianSeriesLimitE (F.squareSummable d)
          (A.comp (P.comp (F.factor d)))) := by
            exact hseries

end ASDExplicitGamma.Native
