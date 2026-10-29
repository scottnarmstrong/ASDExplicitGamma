module

public import ASDExplicitGamma.Gaussian.Q3ModelH3Realization
public import ASDExplicitGamma.Gaussian.GaussianFullConvergence
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import ASDExplicitGamma.Gaussian.GaussMomentHolder
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Function.LpOrder
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Topology.MetricSpace.Bounded
public import ASDExplicitGamma.Gaussian.H3Centering
public import ASDExplicitGamma.Gaussian.C1JetLimit

/-! # Full H³/C¹ convergence and maximal moments for the literal remainder -/

@[expose] public section

open MeasureTheory Homogenization Set Filter
open scoped Topology ENNReal

namespace ASDExplicitGamma.Gaussian

section
variable {ι : Type*} [Countable ι] (a b c d β : ℝ) (L : {l : ℝ // 0 < l})
  (e : HilbertBasis ι ℝ WhiteNoise)

/-- Full partial-sequence convergence in the ordinary H³ realization and the full uniform C¹ jet. -/
theorem ae_tendsto_q3H3Series_full :
    ∀ᵐ ω ∂standardGaussianInfinitePi,
      Tendsto (fun N => gaussianPartialSum (q3H3Directions a b c d β L e) N ω) atTop
        (𝓝 (q3H3Series a b c d β L e ω)) ∧
      Tendsto (fun N => q3H3RangeC1 a b c d β L
        (gaussianPartialSum (q3H3Directions a b c d β L e) N ω)) atTop
        (𝓝 (q3C1Series a b c d β L e ω)) := by
  filter_upwards [@ae_tendsto_gaussianPartialSum (Q3H3Range a b c d β L) inferInstance
    (instQ3H3RangeInnerProductSpace a b c d β L) inferInstance inferInstance inferInstance inferInstance
    (q3H3Directions a b c d β L e) (q3H3Directions_summable a b c d β L e)] with ω hω
  exact ⟨hω, (q3H3RangeC1 a b c d β L).continuous.tendsto _ |>.comp hω⟩

end
end ASDExplicitGamma.Gaussian
