module

public import ASDExplicitGamma.Scalar.LawScalarLimit

/-! The scalar limit reduction used by the long-block no-loss estimate. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization.Book Algsuperdiff.Section3 Filter

/-- An eventual parent-scale bound is enough for the same genuine running
diffusivity ratio; the finite number of small parent cubes do not affect its
limit. -/
theorem sigmaBar_ratio_le_of_annealed_top_entry_eventually_le
    (M : ABKModel 2) (n N : ℤ) (E : ℝ)
    (hE : ∀ᶠ k : ℕ in atTop,
      (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M N) (k : ℤ)).upperLeft 0 0 ≤
        (Annealed.sigmaBar M n : ℝ) * E) :
    (Annealed.sigmaBar M N : ℝ) / (Annealed.sigmaBar M n : ℝ) ≤ E := by
  have hσ : 0 < (Annealed.sigmaBar M n : ℝ) := (Annealed.sigmaBar M n).property
  have hN := le_of_tendsto_of_tendsto (annealed_top_entry_tendsto_sigmaBar M N)
    tendsto_const_nhds hE
  exact (div_le_iff₀ hσ).2 (by nlinarith)

end ASDExplicitGamma.Scalar
