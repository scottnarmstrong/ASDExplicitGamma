module

public import ASDExplicitGamma.Native.HeatVHEATSourceAssembly
public import ASDExplicitGamma.Native.HeatVHEATSourceAuxiliary
public import ASDExplicitGamma.Native.HeatVHEATRefinedAuxiliary
public import ASDExplicitGamma.Native.HeatVHEATCarrierRow
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedObservation
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceClocks
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceNorms
public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedActual
public import ASDExplicitGamma.Native.HeatRefinedFamilyProfiles
public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedExpectation

/-! The differential-only output on the source-normalized carrier. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization ASDExplicitGamma.Gaussian
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Numerics.Native
open scoped ENNReal Topology

/-- The actual source-(8) average cap: the L20 seminorm of the heat-augmented
average of all refined child traces on the common source probability space. -/
noncomputable def nativeHeatQ3RefinedCarrierSourceAverageNorm
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (θ t : ℝ) : ℝ :=
  (eLpNorm
    (heatVHEATDriftRefinedAverage M m t
      (nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian M h hM m θ t))
    20 (nativeHeatRemainderJointLaw M)).toReal

/-- Once the proof supplies the source-normalized expectation row for separate
individual, average, and raw-envelope caps `X`, `Y`, and `F`, the actual
source-carrier moment has the differential-only VHEAT output at the configured
heat parameter. The time-zero cap remains in NA-REFINED-HEAT. -/
theorem nativeHeatQ3RefinedCarrierSourceVHEATBackwardInequality_of_expectationRow
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (X Y F : ℝ)
    (hcaps : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 →
      (heatVHEATDriftRefinedPhysicalXExtended M m t
        (nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian M h hM m
          (nativeHeatTheta : ℝ) t)).toReal ≤ X ∧
      nativeHeatQ3RefinedCarrierSourceAverageNorm M h hM m
          (nativeHeatTheta : ℝ) t ≤ Y ∧
      heatRefinedRawEnvelope 9
        (heatVHEATDriftAuxVariance Finset.univ
          (nativeHeatQ3RefinedCarrierSourceAuxCenterVariance M h hM m
            (nativeHeatTheta : ℝ) t)) ≤ F)
    (hlocal : ∀ k : ℕ, 1 ≤ k → k ≤ 20 → ∀ t : ℝ,
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
          X Y (3 / 10 ^ 46 : ℝ) F) :
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
          X Y (3 / 10 ^ 46 : ℝ) F := by
  have hθ : 0 < (nativeHeatTheta : ℝ) := by norm_num [nativeHeatTheta]
  intro k hk₁ hk₂ t ht
  have hderiv := nativeHeatQ3RefinedCarrierSourceMoment_hasDerivAt
    M h hM m (nativeHeatTheta : ℝ) hθ k (Nat.ne_of_gt (by omega)) ht
  refine ⟨hderiv, ?_⟩
  rw [hderiv.deriv]
  rcases hcaps t ht with ⟨hX, hY, hF⟩
  exact hlocal k hk₁ hk₂ t ht hX hY hF

end ASDExplicitGamma.Native

end
