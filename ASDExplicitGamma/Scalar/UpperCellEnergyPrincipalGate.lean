module

public import ASDExplicitGamma.Scalar.UpperCellEnergyEndpointCertificate

/-! The exact principal cap required before paying the correlated cross term. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open ASDExplicitGamma.Numerics.Scalar ASDExplicitGamma.Numerics.Mirror
noncomputable section

/-- Principal allowance, including the safe old excess and the tiny term. -/
def upperCellPrincipalProfile (gamma z : ℝ) : ℝ :=
  1+z+safeDepth14EndpointCap/2+upperCellSensitivityProfile gamma+
    4*gamma/(3:ℝ)^28

/-- Literal identification of the endpoint principal expression. -/
theorem upper_cell_principal_endpoint :
    upperCellPrincipalProfile gammaZero (9/10) =
      evalReal scalarRealEnv upperPrincipalExpr := by
  unfold upperCellPrincipalProfile
  rw [upper_cell_sensitivity_profile_endpoint]
  norm_num [upperPrincipalExpr,upperSafeSourceExpr,evalReal,sc,gammaZero,
    safeDepth14EndpointCap]

/-- The principal is strictly below two before the cross-term estimate.
This gate uses the upper signal bound, not any target-label lower corridor. -/
theorem upper_cell_principal_lt_two (gamma z : ℝ)
    (hg : gamma ≤ gammaZero) (hz : z ≤ 9/10) :
    upperCellPrincipalProfile gamma z < 2 := by
  have hs := (upper_cell_sensitivity_profile_bounds gamma hg).2
  have ht := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hg (by norm_num : (0:ℝ) ≤ 4))
    (by norm_num : (0:ℝ) ≤ 3^28)
  have hp : upperCellPrincipalProfile gamma z ≤
      upperCellPrincipalProfile gammaZero (9/10) := by
    unfold upperCellPrincipalProfile
    exact add_le_add (add_le_add (add_le_add (add_le_add le_rfl hz) le_rfl) hs) ht
  apply hp.trans_lt
  rw [upper_cell_principal_endpoint]
  exact upper_error_bounds.2.1

/-- The principal-plus-residual triangle is exactly the source error profile. -/
theorem upper_cell_error_decomposition (gamma block z : ℝ) :
    upperCellPrincipalProfile gamma z+
        2*Real.sqrt (2*upperCellResidualProfile gamma block)+
        upperCellResidualProfile gamma block =
      1+z+upperCellErrorProfile gamma block := by
  unfold upperCellPrincipalProfile upperCellErrorProfile
  ring

end
end ASDExplicitGamma.Scalar
