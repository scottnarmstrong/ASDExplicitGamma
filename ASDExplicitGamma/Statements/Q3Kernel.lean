module

public import Algsuperdiff.Frozen.Section3.InductionState
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

@[expose] public section

namespace ASDExplicitGamma

open MeasureTheory ProbabilityTheory Algsuperdiff.Section3
open scoped ENNReal

/-- The normalized one-dimensional q3 kernel `q(x) = √(3003/1024) (1 − 4x²)³` on `|x| ≤ 1/2`, and 0 outside. -/
noncomputable def q3Kernel (x : ℝ) : ℝ :=
  if |x| ≤ 1 / 2 then Real.sqrt (3003 / 1024) * (1 - 4 * x ^ 2) ^ 3 else 0

end ASDExplicitGamma
