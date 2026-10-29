module

public import ASDExplicitGamma.Native.ParentBoundaryCommonKernelProfile

/-! The source quartic kernel as an exact five-term nonnegative polynomial. -/

@[expose] public section
namespace ASDExplicitGamma.Native
noncomputable section

/-- The actual source quartic coefficients, in increasing spatial degree.
The distinct A/B derivative traces and OLD1.856 constant remain literal. -/
def parentBoundaryCommonKernelCoefficients (A2 A4 : ℝ) : Fin 5 → ℝ :=
  let a0 := Real.sqrt (39/5:ℝ)*Real.sqrt A2
  let a1 := (36/25:ℝ)*Real.sqrt (156/5:ℝ)*Real.sqrt A2
  let a2 := (57/200:ℝ)*Real.sqrt (46488/25:ℝ)*Real.sqrt A4
  let b0 := a0
  let b1 := (36/25:ℝ)*Real.sqrt (78/5:ℝ)*Real.sqrt A2
  let b2 := (57/200:ℝ)*Real.sqrt (23244/25:ℝ)*Real.sqrt A4
  ![(232/125:ℝ)*a0^2+38*b0^2,
    2*(232/125:ℝ)*a0*a1+76*b0*b1,
    (232/125:ℝ)*(a1^2+2*a0*a2)+38*(b1^2+2*b0*b2),
    2*(232/125:ℝ)*a1*a2+76*b1*b2,
    (232/125:ℝ)*a2^2+38*b2^2]

/-- Every source quartic coefficient is nonnegative. -/
theorem parent_boundary_common_kernel_coefficients_nonneg (A2 A4 : ℝ) (i : Fin 5) :
    0 ≤ parentBoundaryCommonKernelCoefficients A2 A4 i := by
  fin_cases i <;> norm_num [parentBoundaryCommonKernelCoefficients] <;> positivity

/-- Exact source polynomial expansion, before any geometric ratio is
summed or any outward numerical endpoint is substituted. -/
theorem parent_boundary_common_kernel_profile_polynomial (A2 A4 z : ℝ) :
    parentBoundaryCommonKernelProfile A2 A4 z=
      ∑ i : Fin 5,parentBoundaryCommonKernelCoefficients A2 A4 i*z^i.val := by
  simp only [Fin.sum_univ_succ,Fin.val_zero,Fin.val_succ,Fin.sum_univ_zero,
    parentBoundaryCommonKernelCoefficients,Matrix.cons_val_zero,Matrix.cons_val_succ,
    parentBoundaryCommonKernelProfile]
  ring

end
end ASDExplicitGamma.Native
