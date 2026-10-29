module

public import Algsuperdiff.Frozen.Section3.InductionState
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import ASDExplicitGamma.Statements.Q3Kernel

@[expose] public section

namespace ASDExplicitGamma

open MeasureTheory ProbabilityTheory Algsuperdiff.Section3
open scoped ENNReal

/-- The autocovariance `c(u) = ∫ q(y) q(y + u) dy` of the q3 kernel. -/
noncomputable def q3Cov (u : ℝ) : ℝ :=
  ∫ y, q3Kernel y * q3Kernel (y + u)

end ASDExplicitGamma
