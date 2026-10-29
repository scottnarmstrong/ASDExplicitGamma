module

public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedMeanVariance
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
import ASDExplicitGamma.Gaussian.HilbertBasisVariance
import ASDExplicitGamma.Gaussian.ObservedCovariance

/-! The `ns`-shell generalization of `HeatVHEATBracketRefinedMeanVariance`. -/

@[expose] public section


namespace ASDExplicitGamma.Native

noncomputable section

open MeasureTheory Homogenization ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Main ASDExplicitGamma.Triadic
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ProbabilityTheory
open scoped Topology

variable (ns : ℕ) [NeZero ns]

local instance nativeHeatQ3RefinedMeanVarianceParentCompact_GenBracketRefinedMeanVariance (m : ℤ) :
    CompactSpace (closure (cubeSet (originCube 2 (m + 10)))) :=
  isCompact_iff_compactSpace.mp
    (isBounded_cubeSet (originCube 2 (m + 10))).isCompact_closure

/-- The parent q3 source map used by the actual refined shell law. -/
noncomputable def nativeHeatQ3RefinedCarrierParentSourceGen
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (d : Fin ns) :
    WhiteNoise →L[ℝ]
      C(closure (cubeSet (originCube 2 (m + 10))), ℝ) :=
  let s : ℕ := d.val + 2
  let β := q3ModelAmplitude M h (m + (s : ℤ))
  let L := q3ModelLength (m + (s : ℤ))
  (mainCubeH3Value (m + 10) β L).comp
    (q3H3RangeFactor (-mainCubeHalfSide (m + 10))
      (mainCubeHalfSide (m + 10)) (-mainCubeHalfSide (m + 10))
      (mainCubeHalfSide (m + 10)) β L)

/-- Every scalar observation of the actual refined shell has the same exact
second moment as the Riesz vector of that observation on the parent source. -/
theorem nativeHeatQ3RefinedCarrierParentObservationRiesz_eq_Gen
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ)
    (Ffam : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m ns) (d : Fin ns)
    (A : C(nativeHeatQ3RefinedCarrierDomain m, ℝ) →L[ℝ] ℝ) :
    (∑' j,
      (A ((Ffam).factor d
        ((Ffam).direction d j))) ^ 2) =
      ‖(InnerProductSpace.toDual ℝ WhiteNoise).symm
        ((A.comp (nativeHeatQ3RefinedCarrierParentRestrict m)).comp
          ((nativeHeatQ3RefinedCarrierParentSourceGen ns) M h m d))‖ ^ 2 := by
  classical
  let r := nativeHeatQ3RefinedCarrierParentRestrict m
  let n := m + 10
  let s : ℕ := d.val + 2
  let β := q3ModelAmplitude M h (m + (s : ℤ))
  let L := q3ModelLength (m + (s : ℤ))
  let p := (nativeHeatQ3RefinedCarrierParentSourceGen ns) M h m d
  let B := A.comp r
  let T := mainCubeH3Value n β L
  let v := mainCubeQ3Directions n β L
  have hlabel : nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns d = m + (s : ℤ) := by
    rw [nativeHeatQ3RefinedCarrierPhysicalShellsGen_offset]
  have hLaw :
      standardGaussianInfinitePi.map
          (gaussianSeriesLimitE (Ffam.squareSummable d) (Ffam.factor d)) =
        (standardGaussianInfinitePi.map (mainCubeQ3Series n β L)).map r := by
    simpa [r, n, s, β, L, hlabel,
      nativeHeatQ3RefinedCarrierParentSourceGen] using
      (nativeHeatQ3RefinedCarrierFreshShellParentLaw_Gen ns) M h hM m Ffam d
  have hfactorMeas : Measurable
      (fun ω => gaussianSeriesLimitE (Ffam.squareSummable d) (Ffam.factor d) ω) :=
    (stronglyMeasurable_gaussianSeriesLimitE (Ffam.squareSummable d)
      (Ffam.factor d)).measurable
  let φ : C(nativeHeatQ3RefinedCarrierDomain m, ℝ) → ℝ := fun z => (A z) ^ 2
  have hφ : Measurable φ := by fun_prop
  have hpushF :
      (∫ ω, (A (gaussianSeriesLimitE (Ffam.squareSummable d)
          (Ffam.factor d) ω)) ^ 2 ∂standardGaussianInfinitePi) =
        ∫ z, φ z ∂(standardGaussianInfinitePi.map
          (fun ω => gaussianSeriesLimitE (Ffam.squareSummable d) (Ffam.factor d) ω)) := by
    symm
    exact integral_map hfactorMeas.aemeasurable hφ.aestronglyMeasurable
  have hrmap : Measurable r := r.continuous.measurable
  have hpushR :
      (∫ z, φ z ∂((standardGaussianInfinitePi.map (mainCubeQ3Series n β L)).map r)) =
        ∫ y, (A (r y)) ^ 2 ∂(standardGaussianInfinitePi.map
          (mainCubeQ3Series n β L)) := by
    exact integral_map hrmap.aemeasurable hφ.aestronglyMeasurable
  have hseriesMeas : Measurable (mainCubeQ3Series n β L) := by
    exact (@stronglyMeasurable_gaussianSeriesLimitE
      (MainCubeH3 n β L) C(closure (cubeSet (originCube 2 n)), ℝ)
      inferInstance (mainCubeH3InnerProductSpace n β L)
      inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance
      (mainCubeQ3Directions n β L)
      (mainCubeQ3Directions_summable n β L) (mainCubeH3Value n β L)).measurable
  have hpushT :
      (∫ y, (A (r y)) ^ 2 ∂(standardGaussianInfinitePi.map
          (mainCubeQ3Series n β L))) =
        ∫ ω, (B (mainCubeQ3Series n β L ω)) ^ 2 ∂standardGaussianInfinitePi := by
    simpa [B, ContinuousLinearMap.comp_apply] using
      (integral_map hseriesMeas.aemeasurable
        (show Measurable (fun y => (A (r y)) ^ 2) from by fun_prop).aestronglyMeasurable)
  have hmoment := @integral_observation_sq
    (MainCubeH3 n β L) C(closure (cubeSet (originCube 2 n)), ℝ)
    inferInstance (mainCubeH3InnerProductSpace n β L)
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    (mainCubeQ3Directions n β L) (mainCubeQ3Directions_summable n β L)
    (mainCubeH3Value n β L) B
  have hseriesSum :
      (∫ ω, (B (mainCubeQ3Series n β L ω)) ^ 2 ∂standardGaussianInfinitePi) =
        ∑' j, (B (T (v j))) ^ 2 := by
    exact hmoment
  have hdirection (j : ℕ) :
      T (v j) = gaussEnumerated
        (fun u : whiteBasisIndex => p (whiteBasis u)) j := by
    change mainCubeH3Value n β L
        (gaussEnumerated (fun u : whiteBasisIndex =>
          q3H3RangeFactor (-mainCubeHalfSide n) (mainCubeHalfSide n)
            (-mainCubeHalfSide n) (mainCubeHalfSide n) β L (whiteBasis u)) j) = _
    classical
    let _ := Encodable.ofCountable whiteBasisIndex
    by_cases hj : j ∈ Set.range
        (@Encodable.encode whiteBasisIndex
          (Encodable.ofCountable whiteBasisIndex))
    · obtain ⟨u, rfl⟩ := hj
      rw [enumerated_encode, enumerated_encode]
      rfl
    · rw [gaussEnumerated, Function.extend_apply' _ _ _ hj,
        gaussEnumerated, Function.extend_apply' _ _ _ hj,
        Pi.zero_apply, Pi.zero_apply, map_zero]
  have htsum :
      (∑' j, (B (T (v j))) ^ 2) =
        ∑' u : whiteBasisIndex, (B (p (whiteBasis u))) ^ 2 := by
    calc
      _ = ∑' j, (B (gaussEnumerated
          (fun u : whiteBasisIndex => p (whiteBasis u)) j)) ^ 2 := by
        apply tsum_congr
        intro j
        rw [hdirection j]
      _ = _ := enumerated_tsum_apply
        (fun u : whiteBasisIndex => p (whiteBasis u))
        (fun z => (B z) ^ 2) (by simp)
  have hparseval := hilbertBasis_variance whiteBasis (B.comp p)
  have hparseval' :
      (∑' u : whiteBasisIndex,
        (B (p (whiteBasis u))) ^ 2) =
        ‖(InnerProductSpace.toDual ℝ WhiteNoise).symm (B.comp p)‖ ^ 2 := by
    simpa only [ContinuousLinearMap.comp_apply] using hparseval
  calc
    _ = ∫ ω, (A (gaussianSeriesLimitE (Ffam.squareSummable d)
        (Ffam.factor d) ω)) ^ 2 ∂standardGaussianInfinitePi := by
      symm
      exact integral_observation_sq (Ffam.squareSummable d) (Ffam.factor d) A
    _ = ∫ z, φ z ∂(standardGaussianInfinitePi.map
        (fun ω => gaussianSeriesLimitE (Ffam.squareSummable d) (Ffam.factor d) ω)) := hpushF
    _ = ∫ z, φ z ∂((standardGaussianInfinitePi.map
        (mainCubeQ3Series n β L)).map r) := by rw [hLaw]
    _ = ∫ y, (A (r y)) ^ 2 ∂(standardGaussianInfinitePi.map
        (mainCubeQ3Series n β L)) := hpushR
    _ = ∫ ω, (B (mainCubeQ3Series n β L ω)) ^ 2 ∂standardGaussianInfinitePi := hpushT
    _ = ∑' j, (B (T (v j))) ^ 2 := hseriesSum
    _ = ∑' u : whiteBasisIndex, (B (p (whiteBasis u))) ^ 2 := htsum
    _ = ‖(InnerProductSpace.toDual ℝ WhiteNoise).symm (B.comp p)‖ ^ 2 := hparseval'
    _ = _ := by simp [B, p, r, nativeHeatQ3RefinedCarrierParentSourceGen]

end

end ASDExplicitGamma.Native
