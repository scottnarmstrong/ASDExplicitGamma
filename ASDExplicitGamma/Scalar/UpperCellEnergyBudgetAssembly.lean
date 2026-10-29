module

public import ASDExplicitGamma.Scalar.UpperCellEnergyPrincipalGate

/-! Assembly of the principal and RESET first moments after their physical
estimates. The two moment bounds remain explicit obligations of the producer. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
noncomputable section

/-- Pay the correlated cross term only after proving the principal is below
two. No independence or smaller principal constant is used. -/
theorem upper_cell_energy_triangle_budget
    (gamma block z principal residual : ℝ)
    (hg : gamma ≤ gammaZero) (hz : z ≤ 9/10)
    (hp : principal ≤ upperCellPrincipalProfile gamma z)
    (hr0 : 0 ≤ residual) (hr : residual ≤ upperCellResidualProfile gamma block) :
    principal+2*Real.sqrt (principal*residual)+residual ≤
      1+z+upperCellErrorProfile gamma block := by
  have hp2 : principal ≤ 2 := hp.trans (upper_cell_principal_lt_two gamma z hg hz).le
  have hprod : principal*residual ≤ 2*upperCellResidualProfile gamma block :=
    (mul_le_mul_of_nonneg_right hp2 hr0).trans
      (mul_le_mul_of_nonneg_left hr (by norm_num))
  have hcross := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hprod) (by norm_num : (0:ℝ) ≤ 2)
  have htotal := add_le_add (add_le_add hp hcross) hr
  exact htotal.trans_eq (upper_cell_error_decomposition gamma block z)

end
end ASDExplicitGamma.Scalar
