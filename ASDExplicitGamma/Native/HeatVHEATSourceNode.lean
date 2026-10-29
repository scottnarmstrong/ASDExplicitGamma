/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Native.HeatVHEATSourceExpectation
public import ASDExplicitGamma.Native.HeatVHEATSourceFinalAssembly

/-! The NA-VHEAT-BACKWARD-INEQUALITY node on the source-normalized carrier. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization ASDExplicitGamma.Gaussian
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Numerics.Native

/-- The source-coefficient-4 expectation row on the source carrier. -/
theorem nativeHeatQ3RefinedCarrierSourceExpectationRow
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ l < m + 1, nativeInductionState M h l)
    (hstate : nativeInductionState M h (m + 1))
    (X Y F : ℝ) :
    ∀ k : ℕ, 1 ≤ k → k ≤ 20 → ∀ t : ℝ,
      (ht : t ∈ Set.Ioo (0 : ℝ) 1) →
      ((heatVHEATDriftRefinedPhysicalXExtended M m t
        (nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian M h hM m
          (nativeHeatTheta : ℝ) t)).toReal ≤ X) →
      (nativeHeatQ3RefinedCarrierSourceAverageNorm M h hM m
        (nativeHeatTheta : ℝ) t ≤ Y) →
      (heatRefinedRawEnvelope 9
        (heatVHEATDriftAuxVariance Finset.univ
          (nativeHeatQ3RefinedCarrierSourceAuxCenterVariance M h hM m
            (nativeHeatTheta : ℝ) t)) ≤ F) →
      nativeHeatQ3RefinedCarrierSourceMomentGenerator M h hM m k
          (nativeHeatTheta : ℝ) t ≤
        (k : ℝ) * heatVHEATDriftE9 M *
          (2 * (nativeHeatK : ℝ) * (3683 / 2500 : ℝ) +
            (nativeHeatM : ℝ) * (3683 / 2500 : ℝ) ^ 2) *
          (nativeHeatQ3RefinedCarrierSourceMoment M h hM m k
              (nativeHeatTheta : ℝ) t +
            4 * nativeHeatQ3RefinedCarrierSourceMoment M h hM m (k - 1)
              (nativeHeatTheta : ℝ) t) +
        nativeHeatVHEATErrorEk k 20 (heatVHEATDriftE9 M)
          (nativeHeatK : ℝ) (nativeHeatM : ℝ) (nativeHeatSB : ℝ)
          (nativeHeatTheta : ℝ) (3683 / 2500 : ℝ)
          X Y (3 / 10 ^ 46 : ℝ) F :=
  fun k hk hk20 t ht hX hY hF =>
    nativeHeatQ3RefinedCarrierGeneratorBound M h hM hg m hpast hstate
      k hk hk20 t ht X Y F hX hY hF

/-- NA-VHEAT-BACKWARD-INEQUALITY on the source carrier. -/
theorem nativeHeatVHEATBackwardInequality_source
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ l < m + 1, nativeInductionState M h l)
    (hstate : nativeInductionState M h (m + 1))
    (X Y F : ℝ)
    (hcaps : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 →
      (heatVHEATDriftRefinedPhysicalXExtended M m t
        (nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian M h hM m
          (nativeHeatTheta : ℝ) t)).toReal ≤ X ∧
      nativeHeatQ3RefinedCarrierSourceAverageNorm M h hM m
          (nativeHeatTheta : ℝ) t ≤ Y ∧
      heatRefinedRawEnvelope 9
        (heatVHEATDriftAuxVariance Finset.univ
          (nativeHeatQ3RefinedCarrierSourceAuxCenterVariance M h hM m
            (nativeHeatTheta : ℝ) t)) ≤ F) :
    ∀ k : ℕ, 1 ≤ k → k ≤ 20 → ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 →
      HasDerivAt
        (fun s => nativeHeatQ3RefinedCarrierSourceMoment M h hM m k
          (nativeHeatTheta : ℝ) s)
        (nativeHeatQ3RefinedCarrierSourceMomentGenerator M h hM m k
          (nativeHeatTheta : ℝ) t) t ∧
      deriv (fun s => nativeHeatQ3RefinedCarrierSourceMoment M h hM m k
          (nativeHeatTheta : ℝ) s) t ≤
        (k : ℝ) * heatVHEATDriftE9 M *
          (2 * (nativeHeatK : ℝ) * (3683 / 2500 : ℝ) +
            (nativeHeatM : ℝ) * (3683 / 2500 : ℝ) ^ 2) *
          (nativeHeatQ3RefinedCarrierSourceMoment M h hM m k
              (nativeHeatTheta : ℝ) t +
            4 * nativeHeatQ3RefinedCarrierSourceMoment M h hM m (k - 1)
              (nativeHeatTheta : ℝ) t) +
        nativeHeatVHEATErrorEk k 20 (heatVHEATDriftE9 M)
          (nativeHeatK : ℝ) (nativeHeatM : ℝ) (nativeHeatSB : ℝ)
          (nativeHeatTheta : ℝ) (3683 / 2500 : ℝ)
          X Y (3 / 10 ^ 46 : ℝ) F :=
  nativeHeatQ3RefinedCarrierSourceVHEATBackwardInequality_of_expectationRow
    M h hM m X Y F hcaps
    (nativeHeatQ3RefinedCarrierSourceExpectationRow M h hM hg m hpast hstate X Y F)

end ASDExplicitGamma.Native
