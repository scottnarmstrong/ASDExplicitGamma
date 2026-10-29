module

public import Algsuperdiff.Frozen.Section3.InductionState
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import ASDExplicitGamma.Statements.CutoffTraceDefect

@[expose] public section

namespace ASDExplicitGamma

open MeasureTheory ProbabilityTheory Algsuperdiff.Section3
open scoped ENNReal

/-- The strong mixed history `(1−α) Σ_{r≥0} β₂₀^r ‖T(□_{n−r}; a_n, σ̄_n)‖_{L²⁰}`, with `α = 3^{−1/4}` and
`β₂₀ = 3^{−3/20}` ("strong20"). -/
noncomputable def strong20 (M : ABKModel 2) (n : ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ))) *
    ∑' r : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-(3 / 20 : ℝ) * r)) *
      eLpNorm (cutoffTraceDefect M n (n - r)) 20 (Cutoff.cutoffSampleLaw M).toMeasure

end ASDExplicitGamma
