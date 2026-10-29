module

public import ASDExplicitGamma.StatementProofs.InductionStep
public import Algsuperdiff.Frozen.Section3.InductionState
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import ASDExplicitGamma.Statements.PlanarQ3Gaussian
public import ASDExplicitGamma.Statements.GammaZero
public import ASDExplicitGamma.Statements.NativeInductionState

@[expose] public section

namespace ASDExplicitGamma

open MeasureTheory ProbabilityTheory Algsuperdiff.Section3
open scoped ENNReal

/-- **Gate: induction step.** If the state holds at every strictly earlier label, it holds at `N`. -/
theorem induction_step (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hprev : ∀ n : ℤ, n < N → nativeInductionState M h n) :
    nativeInductionState M h N :=
  by exact ASDExplicitGamma.StatementProofs.induction_step

end ASDExplicitGamma
