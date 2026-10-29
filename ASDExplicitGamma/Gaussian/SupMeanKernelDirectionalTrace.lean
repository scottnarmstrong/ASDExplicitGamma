module

public import ASDExplicitGamma.Gaussian.SupMeanKernelSuccessor
public import ASDExplicitGamma.Gaussian.SupMeanHilbertIncrement

/-! The directional derivative trace is exactly half the isotropic full trace. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization ASDExplicitGamma.Model
open scoped BigOperators RealInnerProductSpace
noncomputable section

/-- Orthogonal coordinate successors retain the exact directional trace. -/
theorem supMean_orthogonal_directional_trace {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {ι : Type*} [Fintype ι] (K0 K1 : ι → H)
    (horth : ∀ i, ⟪K0 i,K1 i⟫ = 0) (v0 v1 : ℝ) :
    (∑ i, ‖v0 • K0 i+v1 • K1 i‖^2) =
      v0^2*(∑ i, ‖K0 i‖^2)+v1^2*(∑ i, ‖K1 i‖^2) := by
  have he (i : ι) : ‖v0 • K0 i+v1 • K1 i‖^2 = v0^2*‖K0 i‖^2+v1^2*‖K1 i‖^2 := by
    rw [norm_add_sq_real, real_inner_smul_left, real_inner_smul_right, horth]
    simp only [mul_zero, add_zero, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  simp_rw [he]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- The scalar product-q3 covariance gives orthogonal skew tensor successors. -/
theorem supMean_kernel_skew_successor_orthogonal (β : ℝ) (L : {l : ℝ // 0 < l})
    (o : Q3SpatialJet) (x : Vec 2) :
    ⟪Real.sqrt 2 • q3Section β L (supMeanKernelJetSuccessor o 0) x,
      Real.sqrt 2 • q3Section β L (supMeanKernelJetSuccessor o 1) x⟫ = 0 := by
  rw [real_inner_smul_left, real_inner_smul_right, supMean_kernel_successor_orthogonal,
    mul_zero, mul_zero]

/-- Exact directional Hessian trace for the first tensor's mean increments. -/
theorem supMean_kernel_first_directional_trace (β : ℝ) (L : {l : ℝ // 0 < l})
    (x v : Vec 2) :
    (∑ i : Fin 2, ‖v 0 • (Real.sqrt 2 • q3Section β L (supMeanKernelJetSuccessor (.first i) 0) x)+
      v 1 • (Real.sqrt 2 • q3Section β L (supMeanKernelJetSuccessor (.first i) 1) x)‖^2) =
        (waveTau2/2)*(β^2/L.val^4)*(v 0^2+v 1^2) := by
  rw [supMean_orthogonal_directional_trace _ _
    (fun i : Fin 2 => supMean_kernel_skew_successor_orthogonal β L (.first i) x),
    supMean_kernel_first_successor_trace, supMean_kernel_first_successor_trace]
  ring

/-- Exact directional third-kernel trace for the stored Hessian's mean increments. -/
theorem supMean_kernel_second_directional_trace (β : ℝ) (L : {l : ℝ // 0 < l})
    (x v : Vec 2) :
    (∑ i : Fin 2 × Fin 2,
      ‖v 0 • (Real.sqrt 2 • q3Section β L (supMeanKernelJetSuccessor (.second i.1 i.2) 0) x)+
        v 1 • (Real.sqrt 2 • q3Section β L (supMeanKernelJetSuccessor (.second i.1 i.2) 1) x)‖^2) =
          (waveTau3/2)*(β^2/L.val^6)*(v 0^2+v 1^2) := by
  rw [supMean_orthogonal_directional_trace _ _
    (fun i : Fin 2 × Fin 2 => supMean_kernel_skew_successor_orthogonal β L (.second i.1 i.2) x),
    supMean_kernel_second_successor_trace, supMean_kernel_second_successor_trace]
  ring

end
end ASDExplicitGamma.Gaussian
