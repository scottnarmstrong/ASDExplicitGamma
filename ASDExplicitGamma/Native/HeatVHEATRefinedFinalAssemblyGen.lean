module

public import ASDExplicitGamma.Native.HeatVHEATRefinedFinalAssembly
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
public import ASDExplicitGamma.Native.HeatVHEATBracketSourceCarrierGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedDriftAssemblyGen
public import ASDExplicitGamma.Native.HeatVHEATSourceBracketGen

/-! The `ns`-shell generalization of `HeatVHEATRefinedFinalAssembly`. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization Gaussian Algsuperdiff.Section3 Numerics.Native
open ASDExplicitGamma.Inverse ASDExplicitGamma.Response ASDExplicitGamma.Variational
open ASDExplicitGamma.Triadic ASDExplicitGamma.Main
open scoped ENNReal NNReal
noncomputable section

variable (ns : ℕ) [NeZero ns]

local instance heatVHEATRefinedFinalChildFiniteGenRefinedFinalAssembly (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    IsFiniteMeasure
      (volumeMeasureOn (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) :=
  ((isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isBoundedDomain).isFiniteMeasure_restrict_volume

local instance heatVHEATRefinedFinalChildCompactGenRefinedFinalAssembly (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    CompactSpace (closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) :=
  isCompact_iff_compactSpace.mp
    (isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isCompact_closure

theorem nativeHeatQ3RefinedCarrierMeanCovariance_minus_center_le_offDiagonal_Gen
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ)
    (Ffam : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m ns) (σ : ℝ) (hσ : 0 < σ)
    (x : ∀ i : nativeHeatQ3RefinedCarrierIndex,
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ)) :
    let Q : nativeHeatQ3RefinedCarrierIndex → TriadicCube 2 :=
      fun i => nativeHeatQ3RefinedCarrierChild m i
    let U : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) := fun i => cubeSet (Q i)
    let hU : ∀ i, MeasurableSet (U i) := fun i => measurableSet_cubeSet (Q i)
    let hvol : ∀ i, 0 < (volume (U i)).toReal := fun i => volume_cubeSet_toReal_pos (Q i)
    let V : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) := fun i => closure (U i)
    let μ := childMeanTrace U hU hvol M.nu σ M.nu_pos hσ
    let I := childConstantMap V
    let C₀ := childCenterMap (nativeHeatQ3RefinedCarrierCenter m)
    let H : ℕ → C(nativeHeatQ3RefinedCarrierDomain m, ℝ) :=
      fun j => nativeHeatQ3RefinedCarrierFreshShellSeriesFactorGen Ffam
        (nativeHeatQ3RefinedCarrierFreshShellSeriesDirectionsGen Ffam j)
    let P := nativeHeatQ3RefinedCarrierOldMap m
    (1 / 2 : ℝ) * modelCovarianceTrace μ (fun j => P (H j)) x -
      (1 / 2 : ℝ) * modelCovarianceTrace μ (fun j => I (C₀ (H j))) x ≤
      ((Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
        ∑ i : nativeHeatQ3RefinedCarrierIndex, ∑ d : Fin ns,
          (nativeHeatQ3RefinedCarrierChildSignedOffDiagonalProfileGen ns)
            M h m i d σ (x i)) := by
  classical
  intro Q U hU hvol V μ I C₀ H P
  have hH : Summable (fun j => ‖H j‖ ^ 2) := by
    change Summable (fun j =>
      ‖nativeHeatQ3RefinedCarrierFreshShellSeriesFactorGen Ffam
        (nativeHeatQ3RefinedCarrierFreshShellSeriesDirectionsGen Ffam j)‖ ^ 2)
    exact summable_sq_norm_map
      (nativeHeatQ3RefinedCarrierFreshShellSeriesSummableGen Ffam)
      (nativeHeatQ3RefinedCarrierFreshShellSeriesFactorGen Ffam)
  have hcard : (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ) =
      ((3 ^ 10 * 3 ^ 10 : ℕ) : ℝ) := by
    norm_num [nativeHeatQ3RefinedCarrierIndex]
  have hmean := nativeHeat_childMeanTrace_covarianceTrace
    Q M.nu σ M.nu_pos hσ hH P x
  have hcenter := (nativeHeatQ3RefinedCarrierMeanCenterCovariance_eq_profileRows_Gen ns)
    M h hM m Ffam σ hσ x
  let childCov : nativeHeatQ3RefinedCarrierIndex → ℝ := fun i =>
    modelCovarianceTrace
      (childTraceObservable (hU i) (hvol i) M.nu σ M.nu_pos hσ)
      (fun j => (P (H j)) i) (x i)
  let childCenter : nativeHeatQ3RefinedCarrierIndex → ℝ := fun i =>
    ∑ d : Fin ns,
      (nativeHeatQ3RefinedCarrierChildCenterDriftProfileGen ns) M h m i d σ (x i)
  let childOff : nativeHeatQ3RefinedCarrierIndex → ℝ := fun i =>
    ∑ d : Fin ns,
      (nativeHeatQ3RefinedCarrierChildSignedOffDiagonalProfileGen ns) M h m i d σ (x i)
  have hchild (i : nativeHeatQ3RefinedCarrierIndex) :
      (1 / 2 : ℝ) * childCov i - childCenter i ≤ childOff i := by
    change (1 / 2 : ℝ) * modelCovarianceTrace
        (childTraceObservable (hU i) (hvol i) M.nu σ M.nu_pos hσ)
        (fun j => (nativeHeatQ3RefinedCarrierOldMap m
          (nativeHeatQ3RefinedCarrierFreshShellSeriesFactorGen Ffam
            (nativeHeatQ3RefinedCarrierFreshShellSeriesDirectionsGen Ffam j))) i)
        (x i) -
        ∑ d : Fin ns,
          (nativeHeatQ3RefinedCarrierChildCenterDriftProfileGen ns) M h m i d σ (x i) ≤
      ∑ d : Fin ns,
        (nativeHeatQ3RefinedCarrierChildSignedOffDiagonalProfileGen ns) M h m i d σ (x i)
    exact (nativeHeatQ3RefinedCarrierChildCenteredCovariance_le_offDiagonalProfiles_Gen ns)
      M h hM m Ffam i σ hσ (x i)
  have hchildsum : (∑ i : nativeHeatQ3RefinedCarrierIndex,
      ((1 / 2 : ℝ) * childCov i - childCenter i)) ≤
      ∑ i : nativeHeatQ3RefinedCarrierIndex, childOff i :=
    Finset.sum_le_sum (fun i _ => hchild i)
  have hcardNonneg : 0 ≤ (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg _)
  have hmean' : modelCovarianceTrace μ (fun j => P (H j)) x =
      (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
        ∑ i : nativeHeatQ3RefinedCarrierIndex, childCov i := by
    rw [hcard]
    exact hmean
  have hcenter' : (1 / 2 : ℝ) * modelCovarianceTrace μ
        (fun j => I (C₀ (H j))) x =
      (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
        ∑ i : nativeHeatQ3RefinedCarrierIndex, childCenter i := by
    change (1 / 2 : ℝ) * modelCovarianceTrace μ
        (fun j => I (C₀ (H j))) x =
      (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
        ∑ i : nativeHeatQ3RefinedCarrierIndex, childCenter i
    exact hcenter
  calc
    _ = (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
        ∑ i : nativeHeatQ3RefinedCarrierIndex,
          ((1 / 2 : ℝ) * childCov i - childCenter i) := by
          rw [hmean', hcenter']
          calc
            _ = (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
                ((1 / 2 : ℝ) *
                    ∑ i : nativeHeatQ3RefinedCarrierIndex, childCov i -
                  ∑ i : nativeHeatQ3RefinedCarrierIndex, childCenter i) := by ring
            _ = (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
                ((∑ i : nativeHeatQ3RefinedCarrierIndex,
                    (1 / 2 : ℝ) * childCov i) -
                  ∑ i : nativeHeatQ3RefinedCarrierIndex, childCenter i) := by
              rw [← Finset.mul_sum]
            _ = _ := by rw [← Finset.sum_sub_distrib]
    _ ≤ (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
        ∑ i : nativeHeatQ3RefinedCarrierIndex, childOff i :=
      mul_le_mul_of_nonneg_left hchildsum hcardNonneg
    _ = (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
        ∑ i : nativeHeatQ3RefinedCarrierIndex, ∑ d : Fin ns,
          (nativeHeatQ3RefinedCarrierChildSignedOffDiagonalProfileGen ns)
            M h m i d σ (x i) := by rfl
