module

public import ASDExplicitGamma.Native.HeatVHEATBracketSourceCarrier
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
public import ASDExplicitGamma.Native.HeatVHEATRefinedRowGen
public import ASDExplicitGamma.Native.Q3GridOverlapGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedSupportGeometryGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedGeometryGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedObservationGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedParentLawGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedSourceMapGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedMeanVarianceGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedRemainderGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedMeanChildBoundGen
public import ASDExplicitGamma.Native.HeatVHEATBracketMeanRieszSupportGen
public import ASDExplicitGamma.Native.HeatVHEATBracketParentRieszGen
public import ASDExplicitGamma.Native.HeatVHEATBracketMeanDerivativeGen
public import ASDExplicitGamma.Native.HeatVHEATBracketMeanDerivativeCLMGen
public import ASDExplicitGamma.Native.HeatVHEATBracketMeanRieszIdentityGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedMeanRieszIdentityGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedMeanAverageProfilesGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedMeanBracketGen

/-! The `ns`-shell generalization of `HeatVHEATBracketSourceCarrier`. -/

@[expose] public section


namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Main ASDExplicitGamma.Model
open scoped Topology

noncomputable section

variable (ns : ℕ) [NeZero ns]

local instance nativeHeatQ3RefinedSourceIndexNeZeroGenBracketSourceCarrier :
    NeZero (3 ^ 10 * 3 ^ 10) := ⟨by norm_num⟩

local instance nativeHeatQ3RefinedSourceDomainCompactGenBracketSourceCarrier (m : ℤ) :
    CompactSpace (nativeHeatQ3RefinedCarrierDomain m) := by
  apply isCompact_iff_compactSpace.mp
  apply isCompact_iUnion
  intro i
  exact (isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isCompact_closure

local instance nativeHeatQ3RefinedSourceChildCompactGenBracketSourceCarrier (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    CompactSpace (closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) :=
  isCompact_iff_compactSpace.mp
    (isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isCompact_closure

local instance nativeHeatQ3RefinedSourceChildFiniteGenBracketSourceCarrier (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    IsFiniteMeasure (volumeMeasureOn (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) :=
  ((isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isBoundedDomain).isFiniteMeasure_restrict_volume

/-- On the physical refined-shell series, the unscaled source center gives
the exact backward-generator identity with the full `(1+θ)` center power
generator. -/
theorem nativeHeatQ3RefinedCarrierSourceCenterCancelledPowerGenerator_eq_Gen
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ)
    (Ffam : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m ns) (σ : ℝ) (hσ : 0 < σ) (θ : ℝ)
    (k : ∀ i : nativeHeatQ3RefinedCarrierIndex,
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ))
    (c : nativeHeatQ3RefinedCarrierIndex → ℝ) (r : ℕ) (hr : 2 ≤ r) :
    let Q : nativeHeatQ3RefinedCarrierIndex → TriadicCube 2 :=
      fun i => nativeHeatQ3RefinedCarrierChild m i
    let U : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) := fun i => cubeSet (Q i)
    let hU : ∀ i, MeasurableSet (U i) := fun i => measurableSet_cubeSet (Q i)
    let hvol : ∀ i, 0 < (volume (U i)).toReal := fun i => volume_cubeSet_toReal_pos (Q i)
    let I := childConstantMap (fun i => closure (U i))
    let μ := childMeanTrace U hU hvol M.nu σ M.nu_pos hσ
    let S := nativeHeatQ3RefinedCarrierFreshShellSeriesFactorGen Ffam
    let W := nativeHeatQ3RefinedCarrierFreshShellSeriesDirectionsGen Ffam
    let P := (nativeHeatQ3RefinedCarrierOldMap m).comp S
    let C₀ := (childCenterMap (nativeHeatQ3RefinedCarrierCenter m)).comp S
    let y := k + I c
    cancelledGenerator W P C₀ I (fun f => μ f ^ r) θ y =
      modelPowerHeatGenerator μ (fun j => P (W j)) (r : ℝ) y -
        (1 + θ) * modelPowerHeatGenerator μ
          (fun j => I (C₀ (W j))) (r : ℝ) y := by
  classical
  intro Q U hU hvol I μ S W P C₀ y
  let Φ : (∀ i : nativeHeatQ3RefinedCarrierIndex,
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ)) → ℝ :=
    fun f => μ f ^ r
  have hW : Summable (fun j => ‖W j‖ ^ 2) :=
    nativeHeatQ3RefinedCarrierFreshShellSeriesSummableGen Ffam
  have hμpoly : HasPolynomiallyBoundedC2Derivatives μ := by
    simpa [μ] using childMeanTrace_polynomial U hU hvol M.nu σ M.nu_pos hσ
  have hμnonneg : ∀ z, 0 ≤ μ z := by
    intro z
    change 0 ≤ childMeanTrace U hU hvol M.nu σ M.nu_pos hσ z
    exact nativeHeat_childMeanTrace_nonneg Q M.nu σ M.nu_pos hσ z
  have hΦC2 : ContDiff ℝ 2 Φ := by
    dsimp [Φ]
    exact hμpoly.1.pow r
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hpowFn : (fun z => μ z ^ (r : ℝ)) = fun z => μ z ^ r := by
    funext z
    exact Real.rpow_natCast (μ z) r
  have hcancel :
      cancelledGenerator W P C₀ I Φ θ y =
        (1 / 2 : ℝ) * modelCovarianceTrace Φ (fun j => P (W j)) y -
          ((1 + θ) / 2) * modelCovarianceTrace Φ
            (fun j => I (C₀ (W j))) y := by
    calc
      _ = backwardGenerator Φ (fun j => P (W j))
          (fun j => I (C₀ (W j))) θ y := by
            exact (congrFun
              (generator_cancellation hW P C₀ I hΦC2 θ) y).symm
      _ = _ := rfl
  have hpowOld := modelCovarianceTrace_rpow hW P μ hμpoly hμnonneg hrR y
  have hpowCenter := modelCovarianceTrace_rpow hW (I.comp C₀) μ
    hμpoly hμnonneg hrR y
  have hpowOld' : (1 / 2 : ℝ) * modelCovarianceTrace Φ
      (fun j => P (W j)) y = modelPowerHeatGenerator μ
        (fun j => P (W j)) (r : ℝ) y := by
    change (1 / 2 : ℝ) * modelCovarianceTrace
      (fun z => μ z ^ r) (fun j => P (W j)) y = _
    rw [← hpowFn]
    exact hpowOld
  have hpowCenter' : (1 / 2 : ℝ) * modelCovarianceTrace Φ
      (fun j => I (C₀ (W j))) y = modelPowerHeatGenerator μ
        (fun j => I (C₀ (W j))) (r : ℝ) y := by
    change (1 / 2 : ℝ) * modelCovarianceTrace
      (fun z => μ z ^ r) (fun j => I (C₀ (W j))) y = _
    rw [← hpowFn]
    exact hpowCenter
  calc
    _ = (1 / 2 : ℝ) * modelCovarianceTrace Φ
          (fun j => P (W j)) y -
        (1 + θ) * ((1 / 2 : ℝ) * modelCovarianceTrace Φ
          (fun j => I (C₀ (W j))) y) := by
          rw [hcancel]
          ring
    _ = _ := by rw [hpowOld', hpowCenter']

