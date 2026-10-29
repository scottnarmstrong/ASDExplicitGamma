module

public import Algsuperdiff.Frozen.Section3.InductionState
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import ASDExplicitGamma.Statements.OrdinaryMean
public import ASDExplicitGamma.Statements.Strong20
public import ASDExplicitGamma.Statements.Root20
public import ASDExplicitGamma.Statements.Buffer40History
public import ASDExplicitGamma.Statements.BufferMean
public import ASDExplicitGamma.Statements.Theta
public import ASDExplicitGamma.Statements.ShellVarianceSum

@[expose] public section

namespace ASDExplicitGamma

open MeasureTheory ProbabilityTheory Algsuperdiff.Section3
open scoped ENNReal

/-- The joint induction state `P(n)` at label `n`:
* the native box with the carried caps, scaled by `θ = γ/γ₀`: ordinary mean ≤ (3/50)θ, strong20 ≤ (2379/2500)θ,
  root20 ≤ (2013/10000)θ, buffer-40 history (`L²⁰` mixed form) ≤ (61/10)θ, buffer-40 mean ≤ (8/25)θ;
* the scalar corridor: ν ≤ σ̄_n, (31/50)B_n + (19/50)ν² ≤ σ̄_n², σ̄_n² ≤ ν² + (13/8)B_n. -/
def nativeInductionState (M : ABKModel 2) (h : ℝ) (n : ℤ) : Prop :=
  ordinaryMean M n ≤ ENNReal.ofReal (3 / 50 * theta M) ∧
  strong20 M n ≤ ENNReal.ofReal (2379 / 2500 * theta M) ∧
  root20 M n ≤ ENNReal.ofReal (2013 / 10000 * theta M) ∧
  buffer40History M n ≤ ENNReal.ofReal (61 / 10 * theta M) ∧
  bufferMean M n ≤ ENNReal.ofReal (8 / 25 * theta M) ∧
  M.nu ≤ (Annealed.sigmaBar M n : ℝ) ∧
  (31 / 50) * shellVarianceSum h M.gamma n + (19 / 50) * M.nu ^ 2 ≤ (Annealed.sigmaBar M n : ℝ) ^ 2 ∧
  (Annealed.sigmaBar M n : ℝ) ^ 2 ≤ M.nu ^ 2 + (13 / 8) * shellVarianceSum h M.gamma n

end ASDExplicitGamma
