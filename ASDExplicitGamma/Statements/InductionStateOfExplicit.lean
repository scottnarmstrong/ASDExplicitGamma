module

public import ASDExplicitGamma.StatementProofs.InductionStateOfExplicit
public import Algsuperdiff.Frozen.Section3.InductionState
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import ASDExplicitGamma.Statements.PlanarQ3Gaussian

@[expose] public section

namespace ASDExplicitGamma

open MeasureTheory ProbabilityTheory Algsuperdiff.Section3
open scoped ENNReal

/-- **T3.** The explicit bounds give the paper's induction state with `E = 2¹⁶` at every scale. -/
theorem inductionState_of_explicit (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ 17 / 50000) (m0 : ℤ) :
    Algsuperdiff.Frozen.Section3.inductionState M m0 ⟨2 ^ 16, by norm_num⟩ :=
  by exact ASDExplicitGamma.StatementProofs.inductionState_of_explicit

end ASDExplicitGamma
