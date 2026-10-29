module

public import ASDExplicitGamma.Gaussian.ModelHeatResponse
public import ASDExplicitGamma.Gaussian.ModelHeatPower

/-! # GA-HEAT for the actual trace defect in the running diffusivity frame -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 Homogenization
open scoped Topology ENNReal

namespace ASDExplicitGamma.Gaussian

/-- The literal model trace-defect expectation during insertion, in the fixed frame σ̄_m.
The symmetric coefficient is `M.nu`, throughout the entire insertion. -/
noncomputable def modelTraceHeatAverage (q : ℤ) (M : ABKModel 2) (m : ℤ) (t : ℝ) : ℝ :=
  ∫ ω, traceDefect (cubeSet (originCube 2 q))
    (Model.partialInsertedCoefficient M m t ω).toFun (Annealed.sigmaBar M m : ℝ)
    ∂(Cutoff.cutoffSampleLaw M).toMeasure

/-- The corresponding literal real moment, averaged over the older and fresh fields. -/
noncomputable def modelTracePowerHeatAverage (q : ℤ) (M : ABKModel 2)
    (m : ℤ) (p t : ℝ) : ℝ :=
  ∫ ω, (traceDefect (cubeSet (originCube 2 q))
    (Model.partialInsertedCoefficient M m t ω).toFun (Annealed.sigmaBar M m : ℝ)) ^ p
    ∂(Cutoff.cutoffSampleLaw M).toMeasure

/-- The literal coarse trace expectation equals its compact continuous-coefficient observable. -/
theorem modelTraceHeatAverage_eq (q : ℤ) (M : ABKModel 2) (m : ℤ) :
    modelTraceHeatAverage q M m =
      modelHeatAverage (closure (cubeSet (originCube 2 q))) M m
        (modelTraceObservable q M.nu (Annealed.sigmaBar M m : ℝ)) := by
  obtain ⟨ell, hK⟩ := exists_originCube_containing_compact _
    (isBounded_cubeSet (originCube 2 q)).isCompact_closure
  funext t
  apply integral_congr_ae
  exact Eventually.of_forall fun ω =>
    (modelTraceObservable_inserted_eq_traceDefect q M ell m hK _ t ω).symm

theorem modelTracePowerHeatAverage_eq (q : ℤ) (M : ABKModel 2) (m : ℤ) (p : ℝ) :
    modelTracePowerHeatAverage q M m p =
      modelHeatAverage (closure (cubeSet (originCube 2 q))) M m
        (fun k => modelTraceObservable q M.nu (Annealed.sigmaBar M m : ℝ) k ^ p) := by
  obtain ⟨ell, hK⟩ := exists_originCube_containing_compact _
    (isBounded_cubeSet (originCube 2 q)).isCompact_closure
  funext t
  apply integral_congr_ae
  exact Eventually.of_forall fun ω => congrArg (fun r : ℝ => r ^ p)
    (modelTraceObservable_inserted_eq_traceDefect q M ell m hK _ t ω).symm

/-- GA-HEAT on the model: C² coefficient regularity, the C¹ heat identity, and all real moment
identities `p ≥ 2`, with ordinary derivatives at every positive time and the right derivative
at zero. Thus all identities hold on `[0,1]`, with its prescribed endpoint convention.
The same fresh-shell realization and physical coefficient directions serve every power. -/
theorem exists_modelTrace_heat_and_moment_identities
    (q : ℤ) (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ) :
    ∃ (T : GaussianFactorL2 ℕ →L[ℝ] C(closure (cubeSet (originCube 2 q)), ℝ))
      (v : ℕ → GaussianFactorL2 ℕ) (hA : Summable (fun j => ‖v j‖ ^ 2)),
      (Cutoff.cutoffSampleLaw M).toMeasure.map
        (fun ω : Cutoff.CutoffSample 2 =>
          shellFieldScalarRestriction (closure (cubeSet (originCube 2 q))) (ω.1 (m + 1))) =
        standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T) ∧
      ContDiff ℝ 2 (modelTraceObservable q M.nu (Annealed.sigmaBar M m : ℝ)) ∧
      ContinuousOn (modelTraceHeatAverage q M m) (Ici 0) ∧
      ContinuousOn (fun t => (1 / 2 : ℝ) *
        modelHeatTraceAverage (closure (cubeSet (originCube 2 q))) M m
          (modelTraceObservable q M.nu (Annealed.sigmaBar M m : ℝ)) (fun j => T (v j)) t) (Ici 0) ∧
      (∀ t ∈ Ioi 0, HasDerivAt (modelTraceHeatAverage q M m)
        ((1 / 2 : ℝ) * modelHeatTraceAverage (closure (cubeSet (originCube 2 q))) M m
          (modelTraceObservable q M.nu (Annealed.sigmaBar M m : ℝ)) (fun j => T (v j)) t) t) ∧
      HasDerivWithinAt (modelTraceHeatAverage q M m)
        ((1 / 2 : ℝ) * modelHeatTraceAverage (closure (cubeSet (originCube 2 q))) M m
          (modelTraceObservable q M.nu (Annealed.sigmaBar M m : ℝ)) (fun j => T (v j)) 0) (Ici 0) 0 ∧
      ∀ p : ℝ, 2 ≤ p →
        ContinuousOn (modelTracePowerHeatAverage q M m p) (Ici 0) ∧
        ContinuousOn (modelHeatAverage (closure (cubeSet (originCube 2 q))) M m
          (modelPowerHeatGenerator (modelTraceObservable q M.nu (Annealed.sigmaBar M m : ℝ))
            (fun j => T (v j)) p)) (Ici 0) ∧
        (∀ t ∈ Ioi 0, HasDerivAt (modelTracePowerHeatAverage q M m p)
          (modelHeatAverage (closure (cubeSet (originCube 2 q))) M m
            (modelPowerHeatGenerator (modelTraceObservable q M.nu (Annealed.sigmaBar M m : ℝ))
              (fun j => T (v j)) p) t) t) ∧
        HasDerivWithinAt (modelTracePowerHeatAverage q M m p)
          (modelHeatAverage (closure (cubeSet (originCube 2 q))) M m
            (modelPowerHeatGenerator (modelTraceObservable q M.nu (Annealed.sigmaBar M m : ℝ))
              (fun j => T (v j)) p) 0) (Ici 0) 0 := by
  let K := closure (cubeSet (originCube 2 q))
  let Φ := modelTraceObservable q M.nu (Annealed.sigmaBar M m : ℝ)
  have hσ : 0 < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).2
  have hΦ : HasPolynomiallyBoundedC2Derivatives Φ :=
    modelTraceObservable_hasPolynomiallyBoundedC2Derivatives q M.nu _ M.nu_pos hσ
  have hnonneg : ∀ k, 0 ≤ Φ k := modelTraceObservable_nonneg q M.nu _ M.nu_pos hσ
  obtain ⟨ell, hK⟩ := exists_originCube_containing_compact K
    (isBounded_cubeSet (originCube 2 q)).isCompact_closure
  obtain ⟨T, v, hA, hlaw⟩ := freshShell_map_scalarRestriction_eq_gaussianSeries M h hM m (K := K)
  have hbase := c1On_modelHeatAverage_of_realization K M ell m hK hA T hlaw Φ hΦ
  refine ⟨T, v, hA, hlaw, hΦ.1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [modelTraceHeatAverage_eq]
    exact hbase.1
  · exact hbase.2.1
  · rw [modelTraceHeatAverage_eq]
    exact hbase.2.2.1
  · rw [modelTraceHeatAverage_eq]
    exact hbase.2.2.2
  · intro p hp
    rw [modelTracePowerHeatAverage_eq]
    exact c1On_modelPowerHeatAverage_of_realization K M ell m hK hA T hlaw Φ hΦ hnonneg hp

end ASDExplicitGamma.Gaussian
