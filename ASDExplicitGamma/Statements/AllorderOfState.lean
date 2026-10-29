module

public import ASDExplicitGamma.StatementProofs.AllorderOfState
public import Algsuperdiff.Frozen.Section3.InductionState
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import ASDExplicitGamma.Statements.PlanarQ3Gaussian
public import ASDExplicitGamma.Statements.GammaZero
public import ASDExplicitGamma.Statements.NativeInductionState
public import ASDExplicitGamma.Statements.AllOrderBounds

@[expose] public section

namespace ASDExplicitGamma

open MeasureTheory ProbabilityTheory Algsuperdiff.Section3
open scoped ENNReal

/-- **Gate: all-order consequence.** The state at every label gives the all-order bounds at every scale. -/
theorem allorder_of_state (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero)
    (hstate : ∀ n : ℤ, nativeInductionState M h n) (m : ℤ) :
    AllOrderBounds M m :=
  by exact ASDExplicitGamma.StatementProofs.allorder_of_state

end ASDExplicitGamma
