module

public import ASDExplicitGamma.Gaussian.ZeroPaddedOrthonormal
public import ASDExplicitGamma.Gaussian.FiniteHilbertFactor

/-! # Orthogonal projections of the joint shell white noise -/

@[expose] public section

open scoped RealInnerProductSpace

namespace ASDExplicitGamma.Gaussian

/-- Separate shell coordinates preserve orthogonality under the common noise enumeration. -/
theorem finiteDirections_orthogonal {b : ℕ} [NeZero b] {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (v : Fin b → ℕ → H)
    (hv : ∀ a, Pairwise (fun i j => ⟪v a i, v a j⟫ = 0)) :
    Pairwise (fun i j => ⟪finiteDirections (fun _ : Fin b => H) v i,
      finiteDirections (fun _ : Fin b => H) v j⟫ = 0) := by
  classical
  intro i j hij
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro a ha
  dsimp only [finiteDirections]
  by_cases hai : a = (bandIndex b i).1
  · subst a
    rw [PiLp.single_eq_same]
    by_cases hs : (bandIndex b i).1 = (bandIndex b j).1
    · rw [hs, PiLp.single_eq_same]
      apply hv _
      intro he
      apply hij
      exact (bandIndex b).injective (Prod.ext hs he)
    · rw [PiLp.single_eq_of_ne 2 hs, inner_zero_right]
  · rw [PiLp.single_eq_of_ne 2 hai, inner_zero_left]

/-- Separate shell coordinates also preserve the unit bound for the input directions. -/
theorem finiteDirections_norm_le_one {b : ℕ} [NeZero b] {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] (v : Fin b → ℕ → H)
    (hv : ∀ a n, ‖v a n‖ ≤ 1) (n : ℕ) :
    ‖finiteDirections (fun _ : Fin b => H) v n‖ ≤ 1 := by
  rw [finiteDirections, PiLp.norm_single]
  exact hv _ _

end ASDExplicitGamma.Gaussian
