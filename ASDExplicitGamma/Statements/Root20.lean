module

public import Algsuperdiff.Frozen.Section3.InductionState
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import ASDExplicitGamma.Statements.CutoffTraceDefect

@[expose] public section

namespace ASDExplicitGamma

open MeasureTheory ProbabilityTheory Algsuperdiff.Section3
open scoped ENNReal

/-- The singleton native `L²⁰` control `‖T(□_n; a_n, σ̄_n)‖_{L²⁰}` ("root20"). -/
noncomputable def root20 (M : ABKModel 2) (n : ℤ) : ℝ≥0∞ :=
  eLpNorm (cutoffTraceDefect M n n) 20 (Cutoff.cutoffSampleLaw M).toMeasure

end ASDExplicitGamma
