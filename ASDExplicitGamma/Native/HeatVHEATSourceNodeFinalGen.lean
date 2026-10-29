module

public import ASDExplicitGamma.Native.HeatVHEATSourceNodeGen
public import ASDExplicitGamma.Native.HeatVHEATSourceNode

/-! The `n`-shell NA-VHEAT-BACKWARD-INEQUALITY node.  The heat step inserts
`n` shells simultaneously; the node holds for every `n` with `9 ≤ n ≤ 1331`
(in particular `9 ≤ n ≤ 160`), with `e_n = (9/2) γ 3^(2 γ n)` in place of
`e_9`. At `n = 9` it recovers the nine-shell main step. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization ASDExplicitGamma.Gaussian
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Numerics.Native

/-- `e_9` is the `n = 9` instance of `e_n`. -/
theorem heatVHEATDriftEGen_nine (M : ABKModel 2) :
    heatVHEATDriftEGen 9 M = heatVHEATDriftE9 M := by
  unfold heatVHEATDriftEGen heatVHEATDriftE9
  congr 2
  push_cast
  ring

/-- NA-VHEAT-BACKWARD-INEQUALITY on the `n`-shell source carrier, for every
`n` with `9 ≤ n ≤ 1331`.  The carrier uses the chosen Gaussian-series
realization of the `n` shells. -/
theorem nativeHeatVHEATBackwardInequality_source_gen
    (n : ℕ) [NeZero n] (hn : 9 ≤ n) (hn1331 : n ≤ 1331)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ l < m + 1, nativeInductionState M h l)
    (hstate : nativeInductionState M h (m + 1))
    (X Y F : ℝ)
    (hcaps : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 →
      ((heatVHEATDriftRefinedPhysicalXExtendedGen n) M m t
        (nativeHeatQ3RefinedCarrierSourceAuxCenterGaussianGen M m n
          (nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m n)
          (nativeHeatTheta : ℝ) t)).toReal ≤ X ∧
      (nativeHeatQ3RefinedCarrierSourceAverageNormGen n) M h hM m
          (nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m n)
          (nativeHeatTheta : ℝ) t ≤ Y ∧
      heatRefinedRawEnvelope n
        (heatVHEATDriftAuxVariance Finset.univ
          (nativeHeatQ3RefinedCarrierSourceAuxCenterVarianceGen M m n
            (nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m n)
            (nativeHeatTheta : ℝ) t)) ≤ F) :
    ∀ k : ℕ, 1 ≤ k → k ≤ 20 → ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 →
      HasDerivAt
        (fun s => nativeHeatQ3RefinedCarrierSourceMomentGen M m n
          (nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m n) k
          (nativeHeatTheta : ℝ) s)
        (nativeHeatQ3RefinedCarrierSourceMomentGeneratorGen M m n
          (nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m n) k
          (nativeHeatTheta : ℝ) t) t ∧
      deriv (fun s => nativeHeatQ3RefinedCarrierSourceMomentGen M m n
          (nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m n) k
          (nativeHeatTheta : ℝ) s) t ≤
        (k : ℝ) * (heatVHEATDriftEGen n) M *
          (2 * (nativeHeatK : ℝ) * (3683 / 2500 : ℝ) +
            (nativeHeatM : ℝ) * (3683 / 2500 : ℝ) ^ 2) *
          (nativeHeatQ3RefinedCarrierSourceMomentGen M m n
              (nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m n) k
              (nativeHeatTheta : ℝ) t +
            4 * nativeHeatQ3RefinedCarrierSourceMomentGen M m n
              (nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m n) (k - 1)
              (nativeHeatTheta : ℝ) t) +
        nativeHeatVHEATErrorEk k 20 ((heatVHEATDriftEGen n) M)
          (nativeHeatK : ℝ) (nativeHeatM : ℝ) (nativeHeatSB : ℝ)
          (nativeHeatTheta : ℝ) (3683 / 2500 : ℝ)
          X Y (3 / 10 ^ 46 : ℝ) F :=
  (nativeHeatVHEATBackwardInequality_source_Gen n hn1331) M h hM hg m
    (nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m n)
    hpast hstate X Y F hcaps

/-- The nine-shell main step is the `n = 9` instance of the
`n`-shell main step. -/
theorem nativeHeatVHEATBackwardInequality_source_of_gen
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
          X Y (3 / 10 ^ 46 : ℝ) F := by
  have hE := heatVHEATDriftEGen_nine M
  have := (nativeHeatVHEATBackwardInequality_source_Gen 9 (by norm_num)) M h hM hg m
    (nativeHeatQ3RefinedCarrierFreshShellFamilyGen_of M h hM m)
    hpast hstate X Y F hcaps
  rw [hE] at this
  exact this

end ASDExplicitGamma.Native
