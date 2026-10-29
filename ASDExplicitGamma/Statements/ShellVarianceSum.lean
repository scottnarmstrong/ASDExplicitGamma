module

public import Algsuperdiff.Frozen.Section3.InductionState
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

@[expose] public section

namespace ASDExplicitGamma

open MeasureTheory ProbabilityTheory Algsuperdiff.Section3
open scoped ENNReal

/-- The accumulated pure shell variance `B_m = Σ_{i ≤ m} h² 3^{2γ i} = h² 3^{2γm} / (1 − 3^{−2γ})`. -/
noncomputable def shellVarianceSum (h γ : ℝ) (m : ℤ) : ℝ :=
  h ^ 2 * (3 : ℝ) ^ (2 * γ * (m : ℝ)) / (1 - (3 : ℝ) ^ (-(2 * γ)))

end ASDExplicitGamma
