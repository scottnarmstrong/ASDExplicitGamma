module

public import ASDExplicitGamma.Gaussian.Q3ContinuousOperator
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-! # Uniform limits of actual first jets remain actual C¹ fields -/

@[expose] public section

open MeasureTheory Homogenization Set Filter
open scoped Topology

namespace ASDExplicitGamma.Gaussian

/-- Extend a jet value arbitrarily off its compact spatial domain; all derivatives below are
asserted on the source open set contained in that domain. -/
noncomputable def c1JetValue {K : Set (Vec 2)} (j : C1Jet K) (x : Vec 2) : ℝ := by
  classical
  exact if hx : x ∈ K then j 0 ⟨x, hx⟩ else 0

end ASDExplicitGamma.Gaussian
