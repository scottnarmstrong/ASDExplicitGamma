module

public import Algsuperdiff.Frozen.Section3.InductionState
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

@[expose] public section

namespace ASDExplicitGamma

open MeasureTheory ProbabilityTheory Algsuperdiff.Section3
open scoped ENNReal

/-- The endpoint `γ₀ = 17/50000`. -/
noncomputable def gammaZero : ℝ := 17 / 50000

end ASDExplicitGamma
