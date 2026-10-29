module

public import ASDExplicitGamma.Gaussian.SupMeanTensorConcentration

/-! A finite covariance Gram bound controls a tensor image of every Hilbert input. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open scoped BigOperators RealInnerProductSpace
noncomputable section

/-- The covariance operator bound, rather than the tensor trace, bounds the
entire Cameron-Martin tensor image of an arbitrary Hilbert vector. -/
theorem supMean_hilbert_tensor_sq_bound {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {ι : Type*} [Fintype ι] (K : ι → H) (M : ℝ) (hM : 0 ≤ M)
    (hgram : ∀ a : ι → ℝ, (∑ i, ∑ j, a i*a j*⟪K i,K j⟫) ≤ M*(∑ i, a i^2)) (u : H) :
    (∑ i, ⟪u,K i⟫^2) ≤ M*‖u‖^2 := by
  let w : ι → ℝ := fun i => ⟪u,K i⟫
  let N := ∑ i, w i^2
  let z : H := ∑ i, w i • K i
  have hN : 0 ≤ N := Finset.sum_nonneg fun i _ => sq_nonneg _
  have huz : ⟪u,z⟫ = N := by
    simp only [z, inner_sum, real_inner_smul_right, N, w]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hzz : ‖z‖^2 = ∑ i, ∑ j, w i*w j*⟪K i,K j⟫ := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [z, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [real_inner_comm (K j) (K i)]
    ring
  have hz : ‖z‖^2 ≤ M*N := by rw [hzz]; exact hgram w
  have hc : N^2 ≤ ‖u‖^2*‖z‖^2 := by
    have hh := sq_le_sq₀ (abs_nonneg ⟪u,z⟫) (mul_nonneg (norm_nonneg u) (norm_nonneg z))
    have hb := hh.mpr (abs_real_inner_le_norm u z)
    simpa only [sq_abs, huz, mul_pow] using hb
  have hb := hc.trans (mul_le_mul_of_nonneg_left hz (sq_nonneg ‖u‖))
  change N ≤ M*‖u‖^2
  by_cases hn : N = 0
  · rw [hn]
    exact mul_nonneg hM (sq_nonneg _)
  · have hp : 0 < N := lt_of_le_of_ne hN (Ne.symm hn)
    nlinarith only [hb,hp]

/-- The squared bound gives the literal Euclidean tensor norm estimate. -/
theorem supMean_hilbert_tensor_norm_bound {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {ι : Type*} [Fintype ι] (K : ι → H) (M : ℝ) (hM : 0 ≤ M)
    (hgram : ∀ a : ι → ℝ, (∑ i, ∑ j, a i*a j*⟪K i,K j⟫) ≤ M*(∑ i, a i^2)) (u : H) :
    ‖(WithLp.toLp 2 (fun i => ⟪u,K i⟫) : EuclideanSpace ℝ ι)‖ ≤ Real.sqrt M*‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg M) (norm_nonneg u))).mp
  rw [EuclideanSpace.real_norm_sq_eq, mul_pow, Real.sq_sqrt hM]
  exact supMean_hilbert_tensor_sq_bound K M hM hgram u

/-- The covariance trace is a valid bound when it is the specified source
operator constant, as for the third weak derivative tensor. -/
theorem supMean_hilbert_tensor_trace_sq_bound {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {ι : Type*} [Fintype ι] (K : ι → H) (u : H) :
    (∑ i, ⟪u,K i⟫^2) ≤ (∑ i, ‖K i‖^2)*‖u‖^2 := by
  calc
    _ ≤ ∑ i, ‖u‖^2*‖K i‖^2 := by
      apply Finset.sum_le_sum
      intro i _
      have hh := (sq_le_sq₀ (abs_nonneg ⟪u,K i⟫)
        (mul_nonneg (norm_nonneg u) (norm_nonneg (K i)))).mpr (abs_real_inner_le_norm u (K i))
      simpa only [sq_abs, mul_pow] using hh
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- Finite kernel combinations have exactly their Gram quadratic norm. -/
theorem supMean_hilbert_combination_norm_sq {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {ι : Type*} [Fintype ι] (K : ι → H) (a : ι → ℝ) :
    ‖∑ i, a i • K i‖^2 = ∑ i, ∑ j, a i*a j*⟪K i,K j⟫ := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [real_inner_comm (K j) (K i)]
  ring

/-- The same operator bound controls every finite kernel linear combination,
by Hilbert duality; the number of coordinates never appears. -/
theorem supMean_hilbert_combination_sq_bound {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {ι : Type*} [Fintype ι] (K : ι → H) (M : ℝ) (hM : 0 ≤ M)
    (hB : ∀ u : H, (∑ i, ⟪u,K i⟫^2) ≤ M*‖u‖^2) (a : ι → ℝ) :
    ‖∑ i, a i • K i‖^2 ≤ M*(∑ i, a i^2) := by
  let z : H := ∑ i, a i • K i
  have he : (∑ i, a i*⟪z,K i⟫) = ‖z‖^2 := by
    calc
      _ = ⟪z,z⟫ := by simp only [z, inner_sum, real_inner_smul_right]
      _ = _ := real_inner_self_eq_norm_sq z
  have hh := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a (fun i => ⟪z,K i⟫)
  rw [he] at hh
  have hb := hh.trans (mul_le_mul_of_nonneg_left (hB z)
    (Finset.sum_nonneg fun i _ => sq_nonneg (a i)))
  change ‖z‖^2 ≤ M*(∑ i, a i^2)
  by_cases hz : ‖z‖ = 0
  · rw [hz, zero_pow (by decide : 2 ≠ 0)]
    exact mul_nonneg hM (Finset.sum_nonneg fun i _ => sq_nonneg (a i))
  · have hp : 0 < ‖z‖^2 := sq_pos_of_ne_zero hz
    nlinarith only [hb,hp]

end
end ASDExplicitGamma.Gaussian
