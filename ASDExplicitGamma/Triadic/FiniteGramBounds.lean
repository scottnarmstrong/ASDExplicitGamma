module

public import ASDExplicitGamma.Triadic.VectorPositiveMultiplier

/-! Finite coefficient bounds from actual, summable covariance Gram rows. -/

@[expose] public section
namespace ASDExplicitGamma.Triadic
open scoped BigOperators
noncomputable section

 theorem finite_coefficient_sq_le_tsum {ι : Type*} (s : Finset ι) (c f : ι → ℝ)
    (hf : Summable (fun l => f l ^ 2)) :
    (∑ l ∈ s, c l*f l)^2 ≤ (∑ l ∈ s, c l^2)*(∑' l, f l^2) := by
  exact (Finset.sum_mul_sq_le_sq_mul_sq s c f).trans
    (mul_le_mul_of_nonneg_left (hf.sum_le_tsum s (fun l _ => sq_nonneg (f l)))
      (Finset.sum_nonneg fun l _ => sq_nonneg (c l)))

 theorem summable_sq_finset_sum {ι κ : Type*} (s : Finset κ) (a : κ → ℝ)
    (X : ι → κ → ℝ) (h : ∀ i ∈ s, ∀ j ∈ s, Summable (fun l => X l i*X l j)) :
    Summable (fun l => (∑ i ∈ s, a i*X l i)^2) := by
  have he (l) : (∑ i ∈ s, a i*X l i)^2 =
      ∑ i ∈ s, ∑ j ∈ s, (a i*a j)*(X l i*X l j) := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp_rw [he]
  exact summable_sum fun i hi => summable_sum fun j hj => (h i hi j hj).mul_left _

 theorem tsum_sq_finset_sum {ι κ : Type*} (s : Finset κ) (a : κ → ℝ)
    (X : ι → κ → ℝ) (h : ∀ i ∈ s, ∀ j ∈ s, Summable (fun l => X l i*X l j)) :
    (∑' l, (∑ i ∈ s, a i*X l i)^2) =
      ∑ i ∈ s, ∑ j ∈ s, (a i*a j)*(∑' l, X l i*X l j) := by
  have he (l) : (∑ i ∈ s, a i*X l i)^2 =
      ∑ i ∈ s, ∑ j ∈ s, (a i*a j)*(X l i*X l j) := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp_rw [he]
  rw [Summable.tsum_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Summable.tsum_finsetSum]
    · simp_rw [tsum_mul_left]
    · exact fun j hj => (h i hi j hj).mul_left _
  · exact fun i hi => summable_sum fun j hj => (h i hi j hj).mul_left _

/-- The operator bound uses the covariance quadratic form, rather than its trace. -/
theorem finite_vector_coefficient_sq_bound {ι κ : Type*} [Fintype κ]
    (X : ι → κ → ℝ) (K : κ → κ → ℝ) (h : ∀ i j, Summable (fun l => X l i*X l j))
    (hK : ∀ i j, (∑' l, X l i*X l j) = K i j) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ a : κ → ℝ, (∑ i, ∑ j, a i*a j*K i j) ≤ M*(∑ i, a i^2))
    (s : Finset ι) (c : ι → ℝ) :
    (∑ i, (∑ l ∈ s, c l*X l i)^2) ≤ M*(∑ l ∈ s, c l^2) := by
  classical
  let w : κ → ℝ := fun i => ∑ l ∈ s, c l*X l i
  let N := ∑ i, w i^2
  have hN : 0 ≤ N := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hs := finite_coefficient_sq_le_tsum s c (fun l => ∑ i, w i*X l i)
    (summable_sq_finset_sum Finset.univ w X (fun i _ j _ => h i j))
  have he : (∑ l ∈ s, c l*(∑ i, w i*X l i)) = N := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [w]
    rw [pow_two, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    ring
  rw [he, tsum_sq_finset_sum Finset.univ w X (fun i _ j _ => h i j)] at hs
  simp_rw [hK] at hs
  have ht := mul_le_mul_of_nonneg_left (hM w) (Finset.sum_nonneg fun l (_ : l ∈ s) => sq_nonneg (c l))
  have hq : N^2 ≤ (∑ l ∈ s, c l^2)*(M*N) := hs.trans ht
  change N ≤ M*(∑ l ∈ s, c l^2)
  by_cases h0 : N = 0
  · rw [h0]
    exact mul_nonneg hM0 (Finset.sum_nonneg fun l _ => sq_nonneg _)
  · have hp : 0 < N := lt_of_le_of_ne hN (Ne.symm h0)
    nlinarith only [hq,hp]

end
end ASDExplicitGamma.Triadic
