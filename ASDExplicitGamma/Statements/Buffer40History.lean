module

public import Algsuperdiff.Frozen.Section3.InductionState
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import ASDExplicitGamma.Statements.CutoffTraceDefect

@[expose] public section

namespace ASDExplicitGamma

open MeasureTheory ProbabilityTheory Algsuperdiff.Section3
open scoped ENNReal

/-- The buffer-40 mixed history `S_{n,40,20} = (1−α) Σ_{r≥0} β₂₀^r ‖T(□_{n−40−r}; a_n, σ̄_n)‖_{L²⁰}` (probability norm
before the depth sum). This is the `p = 20` form returned by the native step; it dominates the `L¹²` random buffered
history consumed by the reset. -/
noncomputable def buffer40History (M : ABKModel 2) (n : ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ))) *
    ∑' r : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-(3 / 20 : ℝ) * r)) *
      eLpNorm (cutoffTraceDefect M n (n - 40 - r)) 20 (Cutoff.cutoffSampleLaw M).toMeasure

end ASDExplicitGamma
