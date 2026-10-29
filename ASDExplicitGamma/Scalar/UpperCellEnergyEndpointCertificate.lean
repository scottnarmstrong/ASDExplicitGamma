module

public import ASDExplicitGamma.Scalar.UpperCellEnergyEndpointMonotone

/-! Exact interpretation and certification of the positive endpoint error. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open ASDExplicitGamma.Numerics.Scalar ASDExplicitGamma.Numerics.Mirror
noncomputable section

/-- The sensitivity formula is exactly the certified arithmetic expression. -/
theorem upper_cell_sensitivity_profile_endpoint :
    upperCellSensitivityProfile gammaZero = evalReal scalarRealEnv upperSensitivityExpr := by
  unfold upperCellSensitivityProfile
  rw [upper_cell_f_profile_endpoint]
  norm_num [upperSensitivityExpr, upperMExpr, evalReal, sc]
  ring

/-- The residual formula is exactly the certified arithmetic expression. -/
theorem upper_cell_residual_profile_endpoint :
    upperCellResidualProfile gammaZero (17/50) = evalReal scalarRealEnv upperResidualExpr := by
  unfold upperCellResidualProfile
  rw [upper_cell_history_profile_endpoint]
  norm_num [upperResidualExpr, evalReal, sc, gammaZero]
  ring

/-- The safe source cap and both correlated cross terms match the certificate. -/
theorem upper_cell_error_profile_endpoint :
    upperCellErrorProfile gammaZero (17/50) = evalReal scalarRealEnv upperErrorExpr := by
  unfold upperCellErrorProfile
  rw [upper_cell_sensitivity_profile_endpoint, upper_cell_residual_profile_endpoint]
  norm_num [upperErrorExpr, upperSafeSourceExpr, evalReal, sc, gammaZero,
    safeDepth14EndpointCap]
  ring

/-- The positive UPPER error is strictly below the certified ceiling throughout
its physical gamma/block rectangle. -/
theorem upper_cell_error_profile_lt (gamma block : ℝ)
    (hg0 : 0 ≤ gamma) (hg : gamma ≤ gammaZero)
    (hb0 : 0 ≤ block) (hb : block ≤ 17/50) :
    upperCellErrorProfile gamma block < 681/10000 := by
  apply (upper_cell_error_profile_le gamma block hg0 hg hb0 hb).trans_lt
  rw [upper_cell_error_profile_endpoint]
  exact upper_error_bounds.1

end
end ASDExplicitGamma.Scalar
