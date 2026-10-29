module

public import ASDExplicitGamma.StatementProofs.ExplicitInductionBounds
public import Algsuperdiff.Frozen.Section3.InductionState
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import ASDExplicitGamma.Statements.PlanarQ3Gaussian
public import ASDExplicitGamma.Statements.ShellVarianceSum
public import ASDExplicitGamma.Statements.AllOrderBounds

@[expose] public section

namespace ASDExplicitGamma

open MeasureTheory ProbabilityTheory Algsuperdiff.Section3
open scoped ENNReal

/-- **T1.** Explicit induction bounds for the planar q3 Gaussian model, `0 < γ ≤ 17/50000`. -/
theorem explicit_induction_bounds (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ 17 / 50000) (m : ℤ) :
    M.nu ≤ (Annealed.sigmaBar M m : ℝ) ∧
    (31 / 50) * shellVarianceSum h M.gamma m + (19 / 50) * M.nu ^ 2 ≤
      (Annealed.sigmaBar M m : ℝ) ^ 2 ∧
    (Annealed.sigmaBar M m : ℝ) ^ 2 ≤ M.nu ^ 2 + (13 / 8) * shellVarianceSum h M.gamma m ∧
    AllOrderBounds M m :=
  by exact ASDExplicitGamma.StatementProofs.explicit_induction_bounds

end ASDExplicitGamma
