module

public import ASDExplicitGamma.Gaussian.SupMeanKernelCovariance

/-! Parity of the literal one-dimensional q3 derivative kernels. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Model MeasureTheory
noncomputable section

/-- The actual weak derivative kernel has parity equal to its derivative order. -/
theorem supMean_kernel_derivative_parity (r : Fin 4) (x : ℝ) :
    q3Derivative r (-x) = (-1:ℝ)^r.val*q3Derivative r x := by
  fin_cases r <;>
    norm_num [q3Derivative, q3Kernel, q3KernelD1, q3KernelD2, q3KernelD3, abs_neg, neg_sq]
  all_goals split_ifs <;> ring

/-- Odd cross-order products have zero ordinary integral, including the
piecewise third derivative at its two cutoff points. -/
theorem supMean_kernel_cross_integral_zero (r s : Fin 4) (hodd : Odd (r.val+s.val)) :
    (∫ x : ℝ, q3Derivative r x*q3Derivative s x) = 0 := by
  have ho (x : ℝ) : q3Derivative r (-x)*q3Derivative s (-x) =
      -(q3Derivative r x*q3Derivative s x) := by
    rw [supMean_kernel_derivative_parity, supMean_kernel_derivative_parity]
    calc
      _ = (-1:ℝ)^(r.val+s.val)*(q3Derivative r x*q3Derivative s x) := by rw [pow_add]; ring
      _ = _ := by rw [hodd.neg_one_pow]; ring
  have he := Measure.integral_comp_mul_left (fun x : ℝ => q3Derivative r x*q3Derivative s x) (-1)
  simp only [neg_one_mul, ho, integral_neg] at he
  norm_num at he
  linarith only [he]

end
end ASDExplicitGamma.Gaussian
