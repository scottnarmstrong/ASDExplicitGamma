module

public import ASDExplicitGamma.Gaussian.HilbertBasisEnumeration
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Finite orthogonal noise projections, including zero-padded bases -/

@[expose] public section

open scoped RealInnerProductSpace

namespace ASDExplicitGamma.Gaussian

/-- Zero padding a countable orthonormal family preserves orthogonality. -/
theorem enumerated_orthogonal {ι H : Type*} [Countable ι] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (e : ι → H) (he : Orthonormal ℝ e) :
    Pairwise (fun i j => ⟪gaussEnumerated e i, gaussEnumerated e j⟫ = 0) := by
  classical
  let := Encodable.ofCountable ι
  intro i j hij
  by_cases hi : i ∈ Set.range (Encodable.encode : ι → ℕ)
  · obtain ⟨a, rfl⟩ := hi
    rw [enumerated_encode]
    by_cases hj : j ∈ Set.range (Encodable.encode : ι → ℕ)
    · obtain ⟨b, rfl⟩ := hj
      rw [enumerated_encode]
      exact he.inner_eq_zero (fun hab => hij (congrArg Encodable.encode hab))
    · rw [gaussEnumerated, Function.extend_apply' _ _ _ hj, Pi.zero_apply, inner_zero_right]
  · rw [gaussEnumerated, Function.extend_apply' _ _ _ hi, Pi.zero_apply, inner_zero_left]

/-- Every padded direction has norm at most one, even for a finite-dimensional noise space. -/
theorem enumerated_norm_le_one {ι H : Type*} [Countable ι] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (e : ι → H) (he : Orthonormal ℝ e) (n : ℕ) :
    ‖gaussEnumerated e n‖ ≤ 1 := by
  classical
  let := Encodable.ofCountable ι
  by_cases hn : n ∈ Set.range (Encodable.encode : ι → ℕ)
  · obtain ⟨a, rfl⟩ := hn
    rw [enumerated_encode, he.norm_eq_one]
  · rw [gaussEnumerated, Function.extend_apply' _ _ _ hn, Pi.zero_apply, norm_zero]
    norm_num

/-- Orthogonal input directions of norm at most one give a contraction on every finite
Euclidean coefficient space. -/
theorem norm_sum_smul_orthogonal_le {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {n : ℕ} (v : Fin n → H)
    (hv : Pairwise (fun i j => ⟪v i, v j⟫ = 0)) (hn : ∀ i, ‖v i‖ ≤ 1)
    (x : EuclideanSpace ℝ (Fin n)) : ‖∑ i, x i • v i‖ ≤ ‖x‖ := by
  classical
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.real_norm_sq_eq]
  simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  apply Finset.sum_le_sum
  intro i hi
  rw [Finset.sum_eq_single i]
  · rw [real_inner_self_eq_norm_sq]
    have hh := pow_le_pow_left₀ (norm_nonneg (v i)) (hn i) 2
    norm_num only [one_pow] at hh
    calc
      _ = x i ^ 2 * ‖v i‖ ^ 2 := by ring
      _ ≤ x i ^ 2 * 1 := mul_le_mul_of_nonneg_left hh (sq_nonneg _)
      _ = _ := mul_one _
  · intro j _ hji
    rw [hv hji.symm, mul_zero, mul_zero]
  · simp

/-- The finite orthogonal input projection as a continuous linear map. -/
noncomputable def orthogonalInputMap {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] {n : ℕ} (v : Fin n → H) : EuclideanSpace ℝ (Fin n) →L[ℝ] H :=
  ∑ i, (PiLp.proj 2 (fun _ : Fin n => ℝ) i).smulRight (v i)

theorem orthogonalInputMap_apply {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] {n : ℕ} (v : Fin n → H) (x : EuclideanSpace ℝ (Fin n)) :
    orthogonalInputMap v x = ∑ i, x i • v i := by
  simp only [orthogonalInputMap, sum_apply, ContinuousLinearMap.smulRight_apply]
  rfl

/-- Its contraction bound is independent of the number of retained noise directions. -/
theorem orthogonalInputMap_norm_le_one {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {n : ℕ} (v : Fin n → H)
    (hv : Pairwise (fun i j => ⟪v i, v j⟫ = 0)) (hn : ∀ i, ‖v i‖ ≤ 1) :
    ‖orthogonalInputMap v‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  rw [orthogonalInputMap_apply, one_mul]
  exact norm_sum_smul_orthogonal_le v hv hn x

end ASDExplicitGamma.Gaussian
