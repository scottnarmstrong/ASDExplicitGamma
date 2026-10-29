module

public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedMeanObservation
public import ASDExplicitGamma.Native.HeatVHEATFamily
import ASDExplicitGamma.Gaussian.HilbertBasisVariance
import ASDExplicitGamma.Gaussian.ObservedCovariance

/-! A scalar observation of an actual refined shell has the same variance as
its canonical parent source, expressed by its white-noise Riesz vector. -/

@[expose] public section

namespace ASDExplicitGamma.Native

noncomputable section

open MeasureTheory Homogenization ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Main ASDExplicitGamma.Triadic
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ProbabilityTheory
open scoped Topology

local instance nativeHeatQ3RefinedMeanVarianceParentCompact (m : ℤ) :
    CompactSpace (closure (cubeSet (originCube 2 (m + 10)))) :=
  isCompact_iff_compactSpace.mp
    (isBounded_cubeSet (originCube 2 (m + 10))).isCompact_closure

/-- The parent q3 source map used by the actual refined shell law. -/
noncomputable def nativeHeatQ3RefinedCarrierParentSource
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (d : Fin 9) :
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
theorem nativeHeatQ3RefinedCarrierParentObservationRiesz_eq
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (d : Fin 9)
    (A : C(nativeHeatQ3RefinedCarrierDomain m, ℝ) →L[ℝ] ℝ) :
    (∑' j,
      (A ((nativeHeatQ3RefinedCarrierFreshShellFamily M h hM m).factor d
        ((nativeHeatQ3RefinedCarrierFreshShellFamily M h hM m).direction d j))) ^ 2) =
      ‖(InnerProductSpace.toDual ℝ WhiteNoise).symm
        ((A.comp (nativeHeatQ3RefinedCarrierParentRestrict m)).comp
          (nativeHeatQ3RefinedCarrierParentSource M h m d))‖ ^ 2 := by
  classical
  let F := nativeHeatQ3RefinedCarrierFreshShellFamily M h hM m
  let r := nativeHeatQ3RefinedCarrierParentRestrict m
  let n := m + 10
  let s : ℕ := d.val + 2
  let β := q3ModelAmplitude M h (m + (s : ℤ))
  let L := q3ModelLength (m + (s : ℤ))
  let p := nativeHeatQ3RefinedCarrierParentSource M h m d
  let B := A.comp r
  let T := mainCubeH3Value n β L
  let v := mainCubeQ3Directions n β L
  have hlabel : nativeHeatQ3RefinedCarrierPhysicalShells m d = m + (s : ℤ) := by
    rw [nativeHeatQ3RefinedCarrierPhysicalShells_offset]
  have hLaw :
      standardGaussianInfinitePi.map
          (gaussianSeriesLimitE (F.squareSummable d) (F.factor d)) =
        (standardGaussianInfinitePi.map (mainCubeQ3Series n β L)).map r := by
    simpa [F, r, n, s, β, L, hlabel,
      nativeHeatQ3RefinedCarrierParentSource] using
      nativeHeatQ3RefinedCarrierFreshShellParentLaw M h hM m d
  have hfactorMeas : Measurable
      (fun ω => gaussianSeriesLimitE (F.squareSummable d) (F.factor d) ω) :=
    (stronglyMeasurable_gaussianSeriesLimitE (F.squareSummable d)
      (F.factor d)).measurable
  let φ : C(nativeHeatQ3RefinedCarrierDomain m, ℝ) → ℝ := fun z => (A z) ^ 2
  have hφ : Measurable φ := by fun_prop
  have hpushF :
      (∫ ω, (A (gaussianSeriesLimitE (F.squareSummable d)
          (F.factor d) ω)) ^ 2 ∂standardGaussianInfinitePi) =
        ∫ z, φ z ∂(standardGaussianInfinitePi.map
          (fun ω => gaussianSeriesLimitE (F.squareSummable d) (F.factor d) ω)) := by
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
    _ = ∫ ω, (A (gaussianSeriesLimitE (F.squareSummable d)
        (F.factor d) ω)) ^ 2 ∂standardGaussianInfinitePi := by
      symm
      exact integral_observation_sq (F.squareSummable d) (F.factor d) A
    _ = ∫ z, φ z ∂(standardGaussianInfinitePi.map
        (fun ω => gaussianSeriesLimitE (F.squareSummable d) (F.factor d) ω)) := hpushF
    _ = ∫ z, φ z ∂((standardGaussianInfinitePi.map
        (mainCubeQ3Series n β L)).map r) := by rw [hLaw]
    _ = ∫ y, (A (r y)) ^ 2 ∂(standardGaussianInfinitePi.map
        (mainCubeQ3Series n β L)) := hpushR
    _ = ∫ ω, (B (mainCubeQ3Series n β L ω)) ^ 2 ∂standardGaussianInfinitePi := hpushT
    _ = ∑' j, (B (T (v j))) ^ 2 := hseriesSum
    _ = ∑' u : whiteBasisIndex, (B (p (whiteBasis u))) ^ 2 := htsum
    _ = ‖(InnerProductSpace.toDual ℝ WhiteNoise).symm (B.comp p)‖ ^ 2 := hparseval'
    _ = _ := by simp [B, p, r, nativeHeatQ3RefinedCarrierParentSource]

end

end ASDExplicitGamma.Native
