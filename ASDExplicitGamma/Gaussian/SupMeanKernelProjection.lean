module

public import ASDExplicitGamma.Gaussian.SupMeanHilbertTensor

/-! Dual projections retain the genuine tensor Cameron-Martin operator constant. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open scoped BigOperators RealInnerProductSpace
noncomputable section

/-- A unit tensor projection of a Hilbert kernel has the same operator bound;
there is no trace or number-of-coordinates loss. -/
theorem supMean_kernel_projection_norm_le {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {ι : Type} [Fintype ι] (K : ι → H)
    (C : ℝ) (hC : 0 ≤ C)
    (hB : ∀ u, ‖(WithLp.toLp 2 (fun i => ⟪u,K i⟫) : EuclideanSpace ℝ ι)‖ ≤ C*‖u‖)
    (v : EuclideanSpace ℝ ι) (hv : ‖v‖ ≤ 1) : ‖∑ i, v i • K i‖ ≤ C := by
  let z := ∑ i, v i • K i
  have he : ⟪v,(WithLp.toLp 2 (fun i => ⟪z,K i⟫) : EuclideanSpace ℝ ι)⟫ = ‖z‖^2 := by
    calc
      _ = ⟪z,z⟫ := by
        simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply,
          star_trivial, z, inner_sum, real_inner_smul_right]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := real_inner_self_eq_norm_sq z
  have hh : ‖z‖^2 ≤ C*‖z‖ := by
    calc
      _ ≤ ‖v‖*‖(WithLp.toLp 2 (fun i => ⟪z,K i⟫) : EuclideanSpace ℝ ι)‖ := by
        rw [← he]
        exact real_inner_le_norm _ _
      _ ≤ ‖(WithLp.toLp 2 (fun i => ⟪z,K i⟫) : EuclideanSpace ℝ ι)‖ := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hv (norm_nonneg _)
      _ ≤ C*‖z‖ := hB z
  change ‖z‖ ≤ C
  nlinarith only [hh, norm_nonneg z, hC]

end
end ASDExplicitGamma.Gaussian
