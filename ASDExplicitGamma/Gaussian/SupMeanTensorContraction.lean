module

public import ASDExplicitGamma.Gaussian.SupMeanHilbertTensor

/-! Exact Euclidean contraction of a spatial two-coordinate tensor. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open scoped BigOperators

/-- Contracting the last two-coordinate slot pays its Euclidean squared length,
without introducing a sup-norm dimensional factor. -/
theorem supMean_tensor_two_coordinate_contraction {ι : Type*} [Fintype ι]
    (T : ι → Fin 2 → ℝ) (v : Fin 2 → ℝ) :
    (∑ i, (v 0*T i 0+v 1*T i 1)^2) ≤
      (v 0^2+v 1^2)*(∑ i, ∑ d : Fin 2, T i d^2) := by
  calc
    _ ≤ ∑ i, (v 0^2+v 1^2)*(T i 0^2+T i 1^2) := by
      apply Finset.sum_le_sum
      intro i _
      nlinarith only [sq_nonneg (v 0*T i 1-v 1*T i 0)]
    _ = _ := by simp only [Fin.sum_univ_two, Finset.mul_sum]

end ASDExplicitGamma.Gaussian
