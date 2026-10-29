module

public import ASDExplicitGamma.Native.HeatVHEATSourceAuxiliary
public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedExpectation

/-! Instantiate the refined source drift expectation on the source
auxiliary Gaussian, including its exact marginal law. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Numerics.Native
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ProbabilityTheory
open scoped ENNReal NNReal

/-- The first-line refined VHEAT expectation row on the actual source carrier.
the coordinate measurability and marginal laws discharge the carrier
inputs, while the construction retains the full actual `9^10` child aggregation. -/
theorem nativeHeatQ3RefinedCarrierSourceDriftExpectation
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ l < m + 1, nativeInductionState M h l)
    (hstate : nativeInductionState M h (m + 1))
    (θ t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (k : ℕ) (hk : 1 ≤ k) (hk20 : k ≤ 20) :
    let g := nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian M h hM m θ t
    let v := nativeHeatQ3RefinedCarrierSourceAuxCenterVariance M h hM m θ t
    let μ := nativeHeatRemainderJointLaw M
    let A := heatVHEATDriftRefinedAverage M m t g
    let X := heatVHEATDriftSourceXExtended Finset.univ M (m + 1) t
      (heatVHEATDriftRefinedShift m) g
    let F := heatRefinedRawEnvelope 9 (heatVHEATDriftAuxVariance Finset.univ v)
    X < ⊤ ∧
      Integrable (heatVHEATDriftRefinedSource M h m t k g) μ ∧
      (∫ z, heatVHEATDriftRefinedSource M h m t k g z ∂μ) ≤
        (k : ℝ) * heatVHEATDriftE9 M *
          (2 * (nativeHeatK : ℝ) * (3683 / 2500 : ℝ) +
            (nativeHeatM : ℝ) * (3683 / 2500 : ℝ) ^ 2) *
          ((∫ z, A z ^ k ∂μ) + 4 * (∫ z, A z ^ (k - 1) ∂μ)) +
        heatVHEATDriftFirstLine k (heatVHEATDriftE9 M)
          nativeHeatK nativeHeatM (3683 / 2500) (3 / 10 ^ 46) X.toReal F := by
  let g := nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian M h hM m θ t
  let v := nativeHeatQ3RefinedCarrierSourceAuxCenterVariance M h hM m θ t
  simpa [g, v] using
    (nativeHeat_vheat_refined_drift_expectation M h hM hg m hpast hstate t ht
      k hk hk20 g
      (fun i => nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian_measurable
        M h hM m θ t i)
      v
      (fun i => nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian_law
        M h hM m θ t i))

end ASDExplicitGamma.Native

end
