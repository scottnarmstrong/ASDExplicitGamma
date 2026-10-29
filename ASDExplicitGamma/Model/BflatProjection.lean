module

public import ASDExplicitGamma.Model.BflatModes
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-! # Finite Bessel bounds inside the Dirichlet projection range -/

@[expose] public section

open scoped BigOperators RealInnerProductSpace

namespace ASDExplicitGamma.Model

/-- A finite orthonormal family lying in a closed subspace measures no more
than the squared norm of the orthogonal projection onto that subspace. -/
theorem bflat_projection_finite_bessel {E ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (V : Submodule ℝ E) [V.HasOrthogonalProjection]
    (e : ι → E) (he : Orthonormal ℝ e) (s : Finset ι)
    (hmem : ∀ i ∈ s, e i ∈ V) (x : E) :
    (∑ i ∈ s, (inner ℝ (e i) x) ^ 2) ≤ ‖V.starProjection x‖ ^ 2 := by
  have horth := V.sub_starProjection_mem_orthogonal x
  have hcoef (i : ι) (hi : i ∈ s) :
      inner ℝ (e i) x = inner ℝ (e i) (V.starProjection x) := by
    have hz := horth (e i) (hmem i hi)
    have hz' : inner ℝ (e i) (x - V.starProjection x) = 0 := by
      simpa only [real_inner_comm] using hz
    rw [inner_sub_right, sub_eq_zero] at hz'
    exact hz'
  have hb := he.sum_inner_products_le (s := s) (x := V.starProjection x)
  calc
    _ = ∑ i ∈ s, (inner ℝ (e i) (V.starProjection x)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hcoef i hi]
    _ ≤ _ := by
      simpa only [Real.norm_eq_abs, sq_abs] using hb

end ASDExplicitGamma.Model
