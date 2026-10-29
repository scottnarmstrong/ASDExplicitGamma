module

public import ASDExplicitGamma.Native.HeatVHEATSourceCarrierGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedShellLaw

/-! Child restrictions of the `n`-shell fresh families (generalizing the nine-shell
nine-shell laws). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open ProbabilityTheory

theorem map_gaussianSeriesLimitE_continuousMap_refinedGen
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
theorem nativeHeatQ3RefinedCarrierChildFreshShellLawGen
    (M : ABKModel 2) (m : ℤ) (n : ℕ)
    (F : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m n)
    (i : nativeHeatQ3RefinedCarrierIndex) (d : Fin n) :
    let P := (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun j : nativeHeatQ3RefinedCarrierIndex =>
        C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m j)), ℝ)) i).comp
      (nativeHeatQ3RefinedCarrierOldMap m)
    let T := P.comp (F.factor d)
    (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω : Cutoff.CutoffSample 2 =>
        shellFieldScalarRestriction
          (closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)))
          (ω.1 (nativeHeatQ3RefinedCarrierPhysicalShellsGen m n d))) =
      standardGaussianInfinitePi.map
        (gaussianSeriesLimitE (F.squareSummable d) T) := by
  classical
  let K := nativeHeatQ3RefinedCarrierDomain m
  let U := closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i))
  let P : C(K, ℝ) →L[ℝ] C(U, ℝ) :=
    (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun j : nativeHeatQ3RefinedCarrierIndex =>
        C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m j)), ℝ)) i).comp
      (nativeHeatQ3RefinedCarrierOldMap m)
  let T := P.comp (F.factor d)
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have hsample : Measurable (fun ω : Cutoff.CutoffSample 2 =>
      shellFieldScalarRestriction K
        (ω.1 (nativeHeatQ3RefinedCarrierPhysicalShellsGen m n d))) :=
    (measurable_shellFieldScalarRestriction K).comp
      ((measurable_pi_apply (nativeHeatQ3RefinedCarrierPhysicalShellsGen m n d)).comp
        measurable_subtype_coe)
  have hrestriction : (fun ω : Cutoff.CutoffSample 2 =>
      P (shellFieldScalarRestriction K
        (ω.1 (nativeHeatQ3RefinedCarrierPhysicalShellsGen m n d)))) =
      (fun ω : Cutoff.CutoffSample 2 =>
        shellFieldScalarRestriction U
          (ω.1 (nativeHeatQ3RefinedCarrierPhysicalShellsGen m n d))) := by
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
    exact map_gaussianSeriesLimitE_continuousMap_refinedGen
      (F.direction d) (F.squareSummable d) (F.factor d) P
  calc
    μ.map (fun ω : Cutoff.CutoffSample 2 =>
        shellFieldScalarRestriction U
          (ω.1 (nativeHeatQ3RefinedCarrierPhysicalShellsGen m n d))) =
      μ.map (fun ω : Cutoff.CutoffSample 2 =>
        P (shellFieldScalarRestriction K
          (ω.1 (nativeHeatQ3RefinedCarrierPhysicalShellsGen m n d)))) := by
            rw [hrestriction]
    _ = Measure.map P (μ.map (fun ω : Cutoff.CutoffSample 2 =>
        shellFieldScalarRestriction K
          (ω.1 (nativeHeatQ3RefinedCarrierPhysicalShellsGen m n d)))) := by
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
theorem nativeHeatQ3RefinedCarrierChildFreshShellOriginLawGen
    (M : ABKModel 2) (m : ℤ) (n : ℕ)
    (F : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m n)
    (i : nativeHeatQ3RefinedCarrierIndex) (d : Fin n) :
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
          (ω.1 (nativeHeatQ3RefinedCarrierPhysicalShellsGen m n d))) =
      standardGaussianInfinitePi.map
        (gaussianSeriesLimitE (F.squareSummable d)
          (A.comp (P.comp (F.factor d)))) := by
  classical
  let Q := nativeHeatQ3RefinedCarrierChild m i
  let U := closure (cubeSet Q)
  let U0 := closure (cubeSet (originCube 2 Q.scale))
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
        (ω.1 (nativeHeatQ3RefinedCarrierPhysicalShellsGen m n d))) :=
    (measurable_shellFieldScalarRestriction U).comp
      ((measurable_pi_apply (nativeHeatQ3RefinedCarrierPhysicalShellsGen m n d)).comp
        measurable_subtype_coe)
  have hchild : μ.map (fun ω : Cutoff.CutoffSample 2 =>
      shellFieldScalarRestriction U
        (ω.1 (nativeHeatQ3RefinedCarrierPhysicalShellsGen m n d))) =
      standardGaussianInfinitePi.map (gaussianSeriesLimitE
        (F.squareSummable d) (P.comp (F.factor d))) := by
    simpa [P, Q, U] using
      (nativeHeatQ3RefinedCarrierChildFreshShellLawGen M m n F i d)
  have htranslate :=
    nativeHeat_shellRestrictionLaw_translateTriadicCube_toOrigin
      M (nativeHeatQ3RefinedCarrierPhysicalShellsGen m n d) Q
  have hseries := map_gaussianSeriesLimitE_continuousMap_refinedGen
    (F.direction d) (F.squareSummable d) (P.comp (F.factor d)) A
  calc
    μ.map (fun ω : Cutoff.CutoffSample 2 =>
        shellFieldScalarRestriction U0
          (ω.1 (nativeHeatQ3RefinedCarrierPhysicalShellsGen m n d))) =
      μ.map (fun ω : Cutoff.CutoffSample 2 => A
        (shellFieldScalarRestriction U
          (ω.1 (nativeHeatQ3RefinedCarrierPhysicalShellsGen m n d)))) := by
            simpa [Q, U, U0, A] using htranslate.symm
    _ = (μ.map (fun ω : Cutoff.CutoffSample 2 =>
        shellFieldScalarRestriction U
          (ω.1 (nativeHeatQ3RefinedCarrierPhysicalShellsGen m n d)))).map A := by
            exact (Measure.map_map A.continuous.measurable hsample).symm
    _ = (standardGaussianInfinitePi.map (gaussianSeriesLimitE
        (F.squareSummable d) (P.comp (F.factor d)))).map A := by
            rw [hchild]
    _ = standardGaussianInfinitePi.map
        (gaussianSeriesLimitE (F.squareSummable d)
          (A.comp (P.comp (F.factor d)))) := by
            exact hseries

end ASDExplicitGamma.Native
