module

public import Algsuperdiff.Frozen.Section3.InductionState
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

@[expose] public section

namespace ASDExplicitGamma

open MeasureTheory ProbabilityTheory Algsuperdiff.Section3
open scoped ENNReal

/-- The all-order conclusions at scale `m`, for every `s ∈ [8γ, 1]`: the two-term `Γ₂/Γ_{1/2}` bound on `E_s` and the
`L^p` moment bound on `E_s²` for every real `p ≥ 1`. -/
def AllOrderBounds (M : ABKModel 2) (m : ℤ) : Prop :=
  ∀ s : ℝ, ∀ hs : s ∈ Set.Icc (8 * M.gamma) 1,
    Probability.IsTwoTermBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
        (Homogenization.IndependentSums.gammaSigma 2)
        (Homogenization.IndependentSums.gammaSigma (1 / 2))
        (Observable.cutoffHomogenizationError M m
          ⟨s, (mul_pos (by norm_num : (0 : ℝ) < 8) M.shellPrefix.gamma_pos).trans_le hs.1⟩)
        (2 ^ 16 * Real.sqrt M.gamma / s)
        (Real.exp (-(Real.log 2 / (8192 * M.gamma)))) ∧
    ∀ p : ℝ, 1 ≤ p →
      eLpNorm
          (fun ω => Observable.cutoffHomogenizationError M m
            ⟨s, (mul_pos (by norm_num : (0 : ℝ) < 8) M.shellPrefix.gamma_pos).trans_le hs.1⟩ ω ^ 2)
          (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal
          (2 ^ 29 * M.gamma * p / s ^ 2 + Real.exp (-(Real.log 2 / (1500 * M.gamma))) * p ^ 3)

end ASDExplicitGamma
