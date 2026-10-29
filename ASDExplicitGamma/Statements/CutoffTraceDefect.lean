module

public import Algsuperdiff.Frozen.Section3.InductionState
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import ASDExplicitGamma.Statements.TraceDefect

@[expose] public section

namespace ASDExplicitGamma

open MeasureTheory ProbabilityTheory Algsuperdiff.Section3
open scoped ENNReal

/-- `T(□_k; a_n, σ̄_n)`: the trace defect of the completed cutoff `a_n` on the origin cube of scale `k`, in the frame of
the true running diffusivity `σ̄_n`. -/
noncomputable def cutoffTraceDefect (M : ABKModel 2) (n k : ℤ) : Cutoff.CutoffSample 2 → ℝ :=
  fun ω => traceDefect (Homogenization.cubeSet (Homogenization.originCube 2 k))
    (Cutoff.coefficientCutoff M.nu n ω).toFun (Annealed.sigmaBar M n : ℝ)

end ASDExplicitGamma
