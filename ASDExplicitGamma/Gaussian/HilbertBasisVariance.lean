module

public import ASDExplicitGamma.Gaussian.CameronMartinFactor
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # Hilbert–Schmidt sums on a covariance kernel complement -/

@[expose] public section

open scoped RealInnerProductSpace

namespace ASDExplicitGamma.Gaussian

/-- Parseval for a continuous linear observation in its input Hilbert space. -/
theorem hilbertBasis_variance {W ι : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] [CompleteSpace W] (e : HilbertBasis ι ℝ W) (l : W →L[ℝ] ℝ) :
    (∑' j, (l (e j)) ^ 2) = ‖(InnerProductSpace.toDual ℝ W).symm l‖ ^ 2 := by
  let z := (InnerProductSpace.toDual ℝ W).symm l
  have he (j : ι) : l (e j) = ⟪z, e j⟫ :=
    (congrArg (fun f : W →L[ℝ] ℝ => f (e j)) ((InnerProductSpace.toDual ℝ W).apply_symm_apply l)).symm
  simp_rw [he]
  calc
    _ = ∑' j, ⟪z, e j⟫ * ⟪e j, z⟫ := by
      apply tsum_congr
      intro j
      rw [real_inner_comm (e j) z, sq]
    _ = _ := (e.tsum_inner_mul_inner z z).trans (real_inner_self_eq_norm_sq z)

/-- Parseval in any output basis expresses the squared output norm. -/
theorem hilbertBasis_norm_sq {H κ : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : HilbertBasis κ ℝ H) (z : H) :
    (∑' k, ⟪f k, z⟫ ^ 2) = ‖z‖ ^ 2 := by
  calc
    _ = ∑' k, ⟪z, f k⟫ * ⟪f k, z⟫ := by
      apply tsum_congr
      intro k
      rw [real_inner_comm z (f k), sq]
    _ = _ := (f.tsum_inner_mul_inner z z).trans (real_inner_self_eq_norm_sq z)

/-- Finite Bessel bounds give square summability without rewriting an infinite sum. -/
theorem hilbertBasis_summable_sq {H κ : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : HilbertBasis κ ℝ H) (z : H) :
    Summable (fun k => ⟪f k, z⟫ ^ 2) := by
  apply summable_of_sum_le (fun _ => sq_nonneg _)
  intro s
  simpa only [Real.norm_eq_abs, sq_abs] using f.orthonormal.sum_inner_products_le (s := s) (x := z)

end ASDExplicitGamma.Gaussian
