module

public import Algsuperdiff.Frozen.Section3.InductionState
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import ASDExplicitGamma.Statements.GammaZero

@[expose] public section

namespace ASDExplicitGamma

open MeasureTheory ProbabilityTheory Algsuperdiff.Section3
open scoped ENNReal

/-- The proportional factor `θ = γ/γ₀` of the native targets. -/
noncomputable def theta (M : ABKModel 2) : ℝ := M.gamma / gammaZero

end ASDExplicitGamma
