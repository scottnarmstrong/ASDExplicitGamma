module

public import ASDExplicitGamma.StatementProofs.MolecularEntrance
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

/-- **Gate: molecular entrance.** The state holds on a left half-line of labels. -/
theorem molecular_entrance (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) :
    ∃ K : ℤ, ∀ n : ℤ, n ≤ K → nativeInductionState M h n :=
  by exact ASDExplicitGamma.StatementProofs.molecular_entrance

end ASDExplicitGamma
