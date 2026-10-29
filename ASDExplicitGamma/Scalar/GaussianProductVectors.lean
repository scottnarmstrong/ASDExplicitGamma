module

public import ASDExplicitGamma.Scalar.GaussianProduct

/-! Finite-dimensional vector Wick bound assembled from the scalar bound. -/
@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- A centered Gaussian coordinate family obeys the same factor-three product
bound for the product of its two squared Euclidean norms. -/
theorem centered_gaussian_vector_product_bound
    {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype ι] [Fintype κ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (Y : κ → Ω → ℝ)
    (hX : ∀ i, HasGaussianLaw (X i) μ) (hY : ∀ j, HasGaussianLaw (Y j) μ)
    (hmX : ∀ i, ∫ ω, X i ω ∂μ = 0) (hmY : ∀ j, ∫ ω, Y j ω ∂μ = 0) :
    (∫ ω, (∑ i, (X i ω)^2) * (∑ j, (Y j ω)^2) ∂μ) ≤
      3 * (∑ i, ∫ ω, (X i ω)^2 ∂μ) * (∑ j, ∫ ω, (Y j ω)^2 ∂μ) := by
  have instHolderFourFourTwo : ENNReal.HolderTriple 4 4 2 := ⟨by
    rw [show (4:ℝ≥0∞) = 2*2 by norm_num, ENNReal.mul_inv, ← add_mul,
      ENNReal.inv_two_add_inv_two, one_mul] <;> norm_num⟩
  have hX4 (i : ι) : MemLp (X i) 4 μ := hX i |>.memLp (by norm_num)
  have hY4 (j : κ) : MemLp (Y j) 4 μ := hY j |>.memLp (by norm_num)
  have hX2 (i : ι) : MemLp (fun ω => (X i ω)^2) 2 μ := by
    simpa only [pow_two] using (hX4 i).fun_mul (hX4 i)
  have hY2 (j : κ) : MemLp (fun ω => (Y j ω)^2) 2 μ := by
    simpa only [pow_two] using (hY4 j).fun_mul (hY4 j)
  have hprod (i : ι) (j : κ) :
      Integrable (fun ω => (X i ω)^2 * (Y j ω)^2) μ :=
    (hX2 i).integrable_mul (hY2 j)
  have hterm (i : ι) (j : κ) :
      (∫ ω, (X i ω)^2 * (Y j ω)^2 ∂μ) ≤
        3 * (∫ ω, (X i ω)^2 ∂μ) * (∫ ω, (Y j ω)^2 ∂μ) :=
    centered_gaussian_product_bound μ (X i) (Y j) (hX i) (hY j) (hmX i) (hmY j)
  have hinner (i : ι) : Integrable
      (fun ω => ∑ j, (X i ω)^2 * (Y j ω)^2) μ :=
    integrable_finsetSum Finset.univ (fun j hj => hprod i j)
  have hfactor :
      3 * (∑ i, ∫ ω, (X i ω)^2 ∂μ) * (∑ j, ∫ ω, (Y j ω)^2 ∂μ) =
        ∑ i, ∑ j, 3 * (∫ ω, (X i ω)^2 ∂μ) * (∫ ω, (Y j ω)^2 ∂μ) := by
    calc
      _ = 3 * ((∑ i, ∫ ω, (X i ω)^2 ∂μ) * (∑ j, ∫ ω, (Y j ω)^2 ∂μ)) := by ring
      _ = 3 * (∑ i, ∑ j,
          (∫ ω, (X i ω)^2 ∂μ) * (∫ ω, (Y j ω)^2 ∂μ)) := by
        rw [Finset.sum_mul_sum]
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
  have hdouble :
      (∫ ω, ∑ i, ∑ j, (X i ω)^2 * (Y j ω)^2 ∂μ) =
        ∑ i, ∑ j, ∫ ω, (X i ω)^2 * (Y j ω)^2 ∂μ := by
    rw [integral_finsetSum Finset.univ (fun i hi => hinner i)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum Finset.univ (fun j hj => hprod i j)]
  calc
    _ = ∑ i, ∑ j, ∫ ω, (X i ω)^2 * (Y j ω)^2 ∂μ := by
      have hpoint (ω : Ω) :
          (∑ i, (X i ω)^2) * (∑ j, (Y j ω)^2) =
            ∑ i, ∑ j, (X i ω)^2 * (Y j ω)^2 := by
        rw [Finset.sum_mul_sum]
      rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
      exact hdouble
    _ ≤ ∑ i, ∑ j, 3 * (∫ ω, (X i ω)^2 ∂μ) * (∫ ω, (Y j ω)^2 ∂μ) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact hterm i j
    _ = _ := hfactor.symm

end ASDExplicitGamma.Scalar
