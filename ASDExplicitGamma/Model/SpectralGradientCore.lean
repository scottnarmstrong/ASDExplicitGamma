module

public import ASDExplicitGamma.Model.SpectralModel

/-!
# The q3 orbit-gradient core

Superdiffusion defines `HasHorizontalGradient φ F` by the strong derivative
at zero of every coordinate Koopman orbit, with values `vectorL2Coord i F`.
The domain is the set of potentials for which such a vector exists. Its
`stationaryPotentialSubspace` closes the range of that full domain.

Here the orbit span and its gradient range are literal restrictions of those
objects. Identifying the closure of this range with
`q3FirstChaosPotentialSubspace` requires the reverse of the inclusion below;
scalar `L²` density alone does not establish it.
-/

@[expose] public section

namespace ASDExplicitGamma.Model

open Algsuperdiff.Probability.Stationary

/-- The algebraic span of the scalar stream translates. -/
noncomputable def q3StreamOrbitSpan (M : Algsuperdiff.Section3.ABKModel 2) :
    Submodule ℝ (ScalarL2 (planarRegLaw M)) :=
  Submodule.span ℝ (Set.range fun z : Homogenization.Vec 2 =>
    q3StreamKoopman M z (q3StreamOriginL2 M))

/-- The range of strong horizontal gradients of algebraic stream combinations. -/
def q3OrbitHorizontalGradientRange (M : Algsuperdiff.Section3.ABKModel 2) :
    Submodule ℝ (VectorL2 2 (planarRegLaw M)) where
  carrier := {F | ∃ φ, φ ∈ q3StreamOrbitSpan M ∧ HasHorizontalGradient φ F}
  zero_mem' := ⟨0, (q3StreamOrbitSpan M).zero_mem, hasHorizontalGradient_zero⟩
  add_mem' := by
    rintro F G ⟨φ, hφ, hdφ⟩ ⟨ψ, hψ, hdψ⟩
    exact ⟨φ + ψ, (q3StreamOrbitSpan M).add_mem hφ hψ, hdφ.add hdψ⟩
  smul_mem' := by
    rintro c F ⟨φ, hφ, hdφ⟩
    exact ⟨c • φ, (q3StreamOrbitSpan M).smul_mem c hφ, hdφ.smul c⟩

/-- Every orbit-span gradient is a gradient with its potential in the first chaos. -/
theorem q3OrbitHorizontalGradientRange_le (M : Algsuperdiff.Section3.ABKModel 2) :
    q3OrbitHorizontalGradientRange M ≤ q3FirstChaosHorizontalGradientRange M := by
  rintro F ⟨φ, hφ, hdφ⟩
  refine ⟨φ, ?_, hdφ⟩
  exact (Submodule.le_topologicalClosure (q3StreamOrbitSpan M)) hφ

/-- One inclusion in the gradient core equality follows from domain inclusion. -/
theorem q3OrbitHorizontalGradientRange_closure_le
    (M : Algsuperdiff.Section3.ABKModel 2) :
    (q3OrbitHorizontalGradientRange M).topologicalClosure ≤
      q3FirstChaosPotentialSubspace M :=
  Submodule.topologicalClosure_mono (q3OrbitHorizontalGradientRange_le M)

end ASDExplicitGamma.Model
