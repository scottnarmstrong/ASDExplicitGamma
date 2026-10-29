module

public import ASDExplicitGamma.Scalar.GaussianHermite

/-! Summing the exact Hermite quartic kernel gives the sharp second-chaos constant 15. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory ASDExplicitGamma.Gaussian

/-- Pure finite algebra for the diagonal Gaussian quadratic fourth moment. -/
theorem diagonal_chaos_fourth_contractions {n : ℕ} (a : Fin n → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, a i*a j*a k*a l*gaussianHermiteFourthKernel i j k l) =
      48*(∑ i, (a i)^4)+12*(∑ i, (a i)^2)^2 := by
  have hsum1 : (∑ i, ∑ j, (a i)^2*(a j)^2) = (∑ i, (a i)^2)^2 := by
    simp_rw [← Finset.mul_sum,← Finset.sum_mul]
    ring
  have hsum2 : (∑ i, a i*(∑ j, a i*(a j)^2)) = (∑ i, (a i)^2)^2 := by
    simp_rw [← Finset.mul_sum,← mul_assoc,← pow_two]
    rw [← Finset.sum_mul]
    ring
  simp_rw [gaussian_hermite_fourth_kernel]
  simp only [mul_add,Finset.sum_add_distrib,ite_and,mul_ite,mul_zero,
    Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  simp only [← Finset.sum_mul]
  ring_nf
  rw [hsum1,hsum2]
  ring

/-- Fourth powers pay no more than the square of the total variance weight. -/
theorem diagonal_fourth_le_square_sum {n : ℕ} (a : Fin n → ℝ) :
    (∑ i, (a i)^4) ≤ (∑ i, (a i)^2)^2 := by
  have h (i : Fin n) : (a i)^2 ≤ ∑ j, (a j)^2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (a j)) (Finset.mem_univ i)
  calc
    _ ≤ ∑ i, (a i)^2*(∑ j, (a j)^2) := Finset.sum_le_sum (fun i _ => by
      have hh := mul_le_mul_of_nonneg_left (h i) (sq_nonneg (a i))
      convert hh using 1
      ring)
    _ = _ := by rw [← Finset.sum_mul]; ring

end ASDExplicitGamma.Scalar
