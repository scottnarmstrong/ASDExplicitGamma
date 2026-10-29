module

public import ASDExplicitGamma.Gaussian.H3KernelSections

/-! Exact same-point one-dimensional q3 jet Gram matrix. -/

@[expose] public section
namespace ASDExplicitGamma.Main
open MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Model

/-- The compact kernel and its first derivative have zero cross moment. -/
theorem main_q3_kernel_first_cross : (∫ x, q3Kernel x*q3KernelD1 x) = 0 := by
  have h := (q3_first_weak_derivatives (q3Kernel_contDiff_two.of_le (by norm_num : (1:WithTop ℕ∞) ≤ 2))).1
  simp_rw [(q3Kernel_hasDerivAt _).deriv] at h
  have he : (fun x => q3KernelD1 x*q3Kernel x) = fun x => q3Kernel x*q3KernelD1 x := by
    funext x; exact mul_comm _ _
  rw [he] at h
  linarith only [h]

/-- The first and second derivatives also have zero cross moment. -/
theorem main_q3_first_second_cross : (∫ x, q3KernelD1 x*q3KernelD2 x) = 0 := by
  have h := (q3_first_weak_derivatives q3KernelD1_contDiff).2
  simp_rw [(gauss_q3KernelD1_hasDerivAt _).deriv] at h
  have he : (fun x => q3KernelD2 x*q3KernelD1 x) = fun x => q3KernelD1 x*q3KernelD2 x := by
    funext x; exact mul_comm _ _
  rw [he] at h
  linarith only [h]

/-- Genuine weak integration by parts supplies the signed 0--2 cross moment. -/
theorem main_q3_kernel_second_cross : (∫ x, q3Kernel x*q3KernelD2 x) = -(78/5:ℝ) := by
  have h := (q3_first_weak_derivatives (q3Kernel_contDiff_two.of_le (by norm_num : (1:WithTop ℕ∞) ≤ 2))).2
  simp_rw [(q3Kernel_hasDerivAt _).deriv, ← pow_two] at h
  rw [q3KernelD1_sq_integral_exact] at h
  have he : (fun x => q3KernelD2 x*q3Kernel x) = fun x => q3Kernel x*q3KernelD2 x := by
    funext x; exact mul_comm _ _
  rw [he] at h
  linarith only [h]

/-- The exact scalar Gram entries through second derivative order. -/
noncomputable def mainQ3KernelGram (r s : Fin 3) : ℝ :=
  if r=s then q3DerivativeMoment ⟨r.val, by omega⟩
  else if r.val+s.val=2 then -(78/5:ℝ) else 0

/-- Every same-point jet pairing is computed, including the signed cross terms. -/
theorem main_q3_kernel_gram (r s : Fin 3) :
    (∫ x, q3Derivative ⟨r.val, by omega⟩ x*q3Derivative ⟨s.val, by omega⟩ x) =
      mainQ3KernelGram r s := by
  have h0 := q3Derivative_integral_sq (0:Fin 4)
  have h1 := q3Derivative_integral_sq (1:Fin 4)
  have h2 := q3Derivative_integral_sq (2:Fin 4)
  fin_cases r <;> fin_cases s <;>
    norm_num [mainQ3KernelGram, q3Derivative, q3DerivativeMoment] at h0 h1 h2 ⊢
  all_goals first
    | simpa only [← pow_two] using h0
    | simpa only [← pow_two] using h1
    | simpa only [← pow_two] using h2
    | exact main_q3_kernel_first_cross
    | exact main_q3_kernel_second_cross
    | exact main_q3_first_second_cross
    | simpa only [mul_comm] using main_q3_kernel_first_cross
    | simpa only [mul_comm] using main_q3_kernel_second_cross
    | simpa only [mul_comm] using main_q3_first_second_cross

end ASDExplicitGamma.Main
