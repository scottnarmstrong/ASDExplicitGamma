module

public import Algsuperdiff.Frozen.Section3.InductionState
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import ASDExplicitGamma.Statements.CutoffTraceDefect

@[expose] public section

namespace ASDExplicitGamma

open MeasureTheory ProbabilityTheory Algsuperdiff.Section3
open scoped ENNReal

/-- The buffer-40 mean `E T(□_{n−40}; a_n, σ̄_n)`. -/
noncomputable def bufferMean (M : ABKModel 2) (n : ℤ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (cutoffTraceDefect M n (n - 40) ω) ∂(Cutoff.cutoffSampleLaw M).toMeasure

end ASDExplicitGamma
