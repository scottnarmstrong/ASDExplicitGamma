module

public import ASDExplicitGamma.Native.HeatVHEATSourceBracket
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

/-! The `ns`-shell generalization of `HeatVHEATSourceBracket`. -/

@[expose] public section


namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Inverse ASDExplicitGamma.Response ASDExplicitGamma.Variational
open ASDExplicitGamma.Triadic ASDExplicitGamma.Main
open scoped ENNReal NNReal Topology

noncomputable section

variable (ns : ℕ) [NeZero ns]

local instance nativeHeatVHEATSourceBracketIndexNeZeroGenSourceBracket :
    NeZero (3 ^ 10 * 3 ^ 10) := ⟨by norm_num⟩

local instance nativeHeatVHEATSourceBracketChildFiniteGenSourceBracket (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    IsFiniteMeasure
      (volumeMeasureOn (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) :=
  ((isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isBoundedDomain).isFiniteMeasure_restrict_volume

/-- The source-carrier second-order bracket has the exact negative excess
center square. Young absorbs it, and the remaining centered shell energy is
bounded by the actual source profiles with no center-clock payment. -/
theorem nativeHeatQ3RefinedCarrierSourceCenteredPowerBracket_le_profileRows_Gen
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ)
    (Ffam : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m ns) (θ : ℝ) (hθ : 0 < θ)
    (x : ∀ i : nativeHeatQ3RefinedCarrierIndex,
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ))
    (r : ℕ) (hr : 2 ≤ r) :
    let Q : nativeHeatQ3RefinedCarrierIndex → TriadicCube 2 :=
      fun i => nativeHeatQ3RefinedCarrierChild m i
    let U : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) := fun i => cubeSet (Q i)
    let hU : ∀ i, MeasurableSet (U i) := fun i => measurableSet_cubeSet (Q i)
    let hvol : ∀ i, 0 < (volume (U i)).toReal := fun i => volume_cubeSet_toReal_pos (Q i)
    let V : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) := fun i => closure (U i)
    let hV : ∀ i, V i ⊆ nativeHeatQ3RefinedCarrierDomain m :=
      nativeHeatQ3RefinedCarrierChild_closure_subset m
    let σ : ℝ := Annealed.sigmaBar M (m + 1)
    let hσ : 0 < σ := (Annealed.sigmaBar_characterization M (m + 1)).1
    let μ := childMeanTrace U hU hvol M.nu σ M.nu_pos hσ
    let I := childConstantMap V
    let C₀ := nativeHeatQ3RefinedCarrierSourceCenterMap m
    let R₀ := childRemainderMap V hV (nativeHeatQ3RefinedCarrierCenter m)
    let L := C₀
    let P := nativeHeatQ3RefinedCarrierOldMap m
    let R := P - I.comp L
    let D := fderiv ℝ μ x
    let coeff := (r : ℝ) * ((r : ℝ) - 1) * (μ x) ^ (r - 2)
    let B : (∀ i, C(V i, ℝ)) →L[ℝ] (∀ i, C(V i, ℝ)) →L[ℝ] ℝ :=
      coeff • D.smulRight D
    let H : ℕ → C(nativeHeatQ3RefinedCarrierDomain m, ℝ) :=
      fun j => nativeHeatQ3RefinedCarrierFreshShellSeriesFactorGen Ffam
        (nativeHeatQ3RefinedCarrierFreshShellSeriesDirectionsGen Ffam j)
    let a : ℕ → ℝ := fun j => D (I (C₀ (H j)))
    let b : ℕ → ℝ := fun j => D (R₀ (H j))
    let sourceRows : ℝ :=
      ∑ d : Fin ns,
        4 * (q3ModelAmplitude M h (m + ((d.val + 2 : ℕ) : ℤ)) ^ 2 / σ ^ 2) *
          q3GridOverlapFactor 10 (d.val + 2) *
          (lemmaVH2Bn
            (cubeScaleFactor (originCube 2 m) /
              (q3ModelLength (m + ((d.val + 2 : ℕ) : ℤ))).1)
            (diagMeshRadius (originCube 2 m)
              (pureFluxBankSourceDepth (d.val + 2)) /
              (q3ModelLength (m + ((d.val + 2 : ℕ) : ℤ))).1)) ^ 2 *
          ((Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
            ∑ i : nativeHeatQ3RefinedCarrierIndex,
              let Q := nativeHeatQ3RefinedCarrierChild m i
              let A := nativeHeat_translateTriadicFieldToOrigin Q
              let k := pureFluxOpenResponseRestriction Q.scale (A (x i))
              let B := lemmaVTileHistory (originCube 2 Q.scale)
                (pureFluxBankSourceDepth (d.val + 2))
                (responseFramePlanarCoefficientField M.nu σ k)
              let T := modelTraceObservable Q.scale M.nu σ (A (x i))
              B ^ 2 * T * (T + 4));
    (-θ * centerGenerator H L I B +
      mixedGenerator H L I R B +
      (1 / 2 : ℝ) * ∑' j, B (R (H j)) (R (H j))) =
        coeff * (-(θ / 2) * ∑' j, (a j) ^ 2 +
          ∑' j, a j * b j + (1 / 2 : ℝ) * ∑' j, (b j) ^ 2) ∧
    (-θ * centerGenerator H L I B +
      mixedGenerator H L I R B +
      (1 / 2 : ℝ) * ∑' j, B (R (H j)) (R (H j)) ≤
        (coeff / 2) * ((1 + θ⁻¹) * sourceRows)) := by
  classical
  intro Q U hU hvol V hV σ hσ μ I C₀ R₀ L P R D coeff B H a b sourceRows
  have hH : Summable (fun j => ‖H j‖ ^ 2) := by
    change Summable (fun j =>
      ‖nativeHeatQ3RefinedCarrierFreshShellSeriesFactorGen Ffam
        (nativeHeatQ3RefinedCarrierFreshShellSeriesDirectionsGen Ffam j)‖ ^ 2)
    exact summable_sq_norm_map
      (nativeHeatQ3RefinedCarrierFreshShellSeriesSummableGen Ffam)
      (nativeHeatQ3RefinedCarrierFreshShellSeriesFactorGen Ffam)
  have hYoung := nativeHeatQ3RefinedCarrierSourceCenterRankOneResidualSplit
    M m θ hθ H hH x r hr
  have hRank :
      -θ * centerGenerator H L I B +
        mixedGenerator H L I R B +
        (1 / 2 : ℝ) * ∑' j, B (R (H j)) (R (H j)) =
      coeff * (-(θ / 2) * ∑' j, (a j) ^ 2 +
        ∑' j, a j * b j + (1 / 2 : ℝ) * ∑' j, (b j) ^ 2) := by
    exact hYoung.1
  have hYoungBound :
      -θ * centerGenerator H L I B +
        mixedGenerator H L I R B +
        (1 / 2 : ℝ) * ∑' j, B (R (H j)) (R (H j)) ≤
      (coeff / 2) * ((1 + θ⁻¹) * ∑' j, (b j) ^ 2) := by
    exact hYoung.2
  have hrow := (nativeHeatQ3RefinedCarrierMeanRemainderBracket_sum_Gen ns)
    M h hM m Ffam σ hσ x
  have hweighted := (nativeHeatQ3RefinedCarrierPowerCenteredBracket_le_profileRows_Gen ns)
    M h hM m Ffam σ hσ x r hr θ hθ hrow
  have hμnonneg : 0 ≤ μ x :=
    nativeHeat_childMeanTrace_nonneg (nativeHeatQ3RefinedCarrierChild m)
      M.nu σ M.nu_pos hσ x
  have hpow : Real.rpow (μ x) ((r : ℝ) - 2) = (μ x) ^ (r - 2) := by
    have hcast : ((r - 2 : ℕ) : ℝ) = (r : ℝ) - 2 := by
      exact Nat.cast_sub hr
    rw [← hcast]
    exact Real.rpow_natCast _ _
  have hcoeffEq : (coeff / 2) * (1 + θ⁻¹) =
      ((r : ℝ) * ((r : ℝ) - 1) / 2) * (1 + θ⁻¹) *
        Real.rpow (μ x) ((r : ℝ) - 2) := by
    dsimp only [coeff]
    rw [hpow]
    ring
  have hgrad : modelGradientSquareTrace μ (fun j => R₀ (H j)) x =
      ∑' j, (b j) ^ 2 := by
    unfold modelGradientSquareTrace
    rfl
  have hweightedExact :
      (((r : ℝ) * ((r : ℝ) - 1) / 2) * (1 + θ⁻¹) *
        Real.rpow (μ x) ((r : ℝ) - 2)) *
          modelGradientSquareTrace μ (fun j => R₀ (H j)) x ≤
      (((r : ℝ) * ((r : ℝ) - 1) / 2) * (1 + θ⁻¹) *
        Real.rpow (μ x) ((r : ℝ) - 2)) * sourceRows := by
    simpa only [sourceRows] using hweighted
  have hweighted' :
      (coeff / 2) * (1 + θ⁻¹) * modelGradientSquareTrace μ
        (fun j => R₀ (H j)) x ≤ (coeff / 2) * (1 + θ⁻¹) * sourceRows := by
    calc
      _ = (((r : ℝ) * ((r : ℝ) - 1) / 2) * (1 + θ⁻¹) *
          Real.rpow (μ x) ((r : ℝ) - 2)) *
            modelGradientSquareTrace μ (fun j => R₀ (H j)) x := by
              rw [hcoeffEq]
      _ ≤ (((r : ℝ) * ((r : ℝ) - 1) / 2) * (1 + θ⁻¹) *
          Real.rpow (μ x) ((r : ℝ) - 2)) * sourceRows := hweightedExact
      _ = _ := by rw [← hcoeffEq]
  refine ⟨hRank, ?_⟩
  calc
    _ ≤ (coeff / 2) * ((1 + θ⁻¹) * ∑' j, (b j) ^ 2) := hYoungBound
    _ = (coeff / 2) * (1 + θ⁻¹) * modelGradientSquareTrace μ
        (fun j => R₀ (H j)) x := by rw [hgrad]; ring
    _ ≤ (coeff / 2) * (1 + θ⁻¹) * sourceRows := hweighted'
    _ = (coeff / 2) * ((1 + θ⁻¹) * sourceRows) := by ring

