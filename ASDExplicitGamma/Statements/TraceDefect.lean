module

public import Algsuperdiff.Frozen.Section3.InductionState
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

@[expose] public section

namespace ASDExplicitGamma

open MeasureTheory ProbabilityTheory Algsuperdiff.Section3
open scoped ENNReal

/-- The normalized four-load trace defect `T(U; a, σ) = σ⁻¹ tr A₁₁(U; a) + σ tr A₂₂(U; a) − 4` of the coarse doubled
matrix `A(U; a)`, in the scalar frame `σ`. -/
noncomputable def traceDefect (U : Set (Homogenization.Vec 2)) (a : Homogenization.CoeffField 2) (σ : ℝ) : ℝ :=
  σ⁻¹ * Matrix.trace (Homogenization.coarseBlockMatrix U a).upperLeft +
    σ * Matrix.trace (Homogenization.coarseBlockMatrix U a).lowerRight - 4

end ASDExplicitGamma
