module

public import Algsuperdiff.Frozen.Section3.InductionState
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import ASDExplicitGamma.Statements.Q3Cov

@[expose] public section

namespace ASDExplicitGamma

open MeasureTheory ProbabilityTheory Algsuperdiff.Section3
open scoped ENNReal

/-- The planar product-q3 Gaussian law at amplitude `h > 0`: under the zero-shell law of `M`, for every finite family
of points `x i` and coefficients `t i`, the random variable `Σ t i · ψ(x i)` is centered Gaussian with variance
`h² Σ_{i,i'} t i t i' c((x i − x i')₀) c((x i − x i')₁)`. Here `ψ = (j₀)₁₀` is the scalar stream of the skew shell
`j₀ = ψ J`, `J = [[0,-1],[1,0]]`. Independence of shells and exact triadic scaling are part of `ABKModel`. -/
def PlanarQ3Gaussian (M : ABKModel 2) (h : ℝ) : Prop :=
  0 < h ∧
    ∀ (n : ℕ) (x : Fin n → Homogenization.Vec 2) (t : Fin n → ℝ),
      (Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellLaw M.P).toMeasure.map
          (fun j : Algsuperdiff.Frozen.Assumptions.ShellField 2 => ∑ i, t i * (j (x i)) 1 0) =
        gaussianReal 0
          (Real.toNNReal
            (h ^ 2 * ∑ i, ∑ i', t i * t i' *
              q3Cov ((x i - x i') 0) * q3Cov ((x i - x i') 1)))

end ASDExplicitGamma
