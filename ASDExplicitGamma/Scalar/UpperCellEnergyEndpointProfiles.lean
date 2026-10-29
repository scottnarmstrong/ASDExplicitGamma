module

public import ASDExplicitGamma.Scalar.UpperSourceCaps
public import ASDExplicitGamma.Numerics.Scalar.Upper

/-! Positive UPPER error profiles at the actual dimensionless block length.
These are the formulas of UPPER_PROOF section 2, with the safe source cap. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open ASDExplicitGamma.Numerics.Scalar ASDExplicitGamma.Numerics.Mirror
noncomputable section

/-- Complete future full64 history majorant, including the finite frame denominator. -/
def upperCellHistoryProfile (gamma block : ℝ) : ℝ :=
  4*((1130469/10^6:ℝ)*(1009309/500000)+
    16684*((1130469/10^6:ℝ)*(block+15*gamma)+gamma*(838143/200000))+
    gamma*5899542*(1130469/10^6:ℝ))/(1-(11/10:ℝ)*(2*block+60*gamma))

/-- The physical depth-fourteen sensitivity scale. -/
def upperCellFProfile (gamma : ℝ) : ℝ := 64*Real.sqrt gamma/(3:ℝ)^14

/-- The complete positive sensitivity allowance at the source history cap. -/
def upperCellSensitivityProfile (gamma : ℝ) : ℝ :=
  24*(1+2*(61/10:ℝ)+Real.sqrt (2*(61/10:ℝ)))^2*
    (upperCellFProfile gamma+2*(upperCellFProfile gamma)^2+
      4*(upperCellFProfile gamma)^3)

/-- The RESET residual allowance with the complete new full-response history. -/
def upperCellResidualProfile (gamma block : ℝ) : ℝ :=
  10*upperCellHistoryProfile gamma block*gamma/(3:ℝ)^28

/-- The complete positive UPPER error, with the two correlated cross terms. -/
def upperCellErrorProfile (gamma block : ℝ) : ℝ :=
  safeDepth14EndpointCap/2+upperCellSensitivityProfile gamma+
    2*Real.sqrt (2*upperCellResidualProfile gamma block)+
    upperCellResidualProfile gamma block+4*gamma/(3:ℝ)^28

/-- The source frame denominator stays positive on the whole smaller-gamma block range. -/
theorem upper_cell_profile_denominator_pos (gamma block : ℝ)
    (hg : gamma ≤ gammaZero) (hb : block ≤ 17/50) :
    0 < 1-(11/10:ℝ)*(2*block+60*gamma) := by
  change gamma ≤ 17/50000 at hg
  linarith only [hg,hb]

/-- Exact endpoint interpretation of the history profile in the certified expression. -/
theorem upper_cell_history_profile_endpoint :
    upperCellHistoryProfile gammaZero (17/50) =
      evalReal scalarRealEnv upperMnewExpr := by
  norm_num [upperCellHistoryProfile,gammaZero,upperMnewExpr,evalReal,sc]

/-- Exact endpoint interpretation of the sensitivity scale. -/
theorem upper_cell_f_profile_endpoint :
    upperCellFProfile gammaZero = evalReal scalarRealEnv upperFExpr := by
  norm_num [upperCellFProfile,gammaZero,upperFExpr,evalReal,sc]
  ring

/-- The physical f term retains its exact square-root theta factor. -/
theorem upper_cell_f_profile_scaling (gamma : ℝ) (hg : 0 ≤ gamma) :
    upperCellFProfile gamma =
      Real.sqrt (gamma/gammaZero)*upperCellFProfile gammaZero := by
  rw [upperCellFProfile,upperCellFProfile,Real.sqrt_div hg]
  have hz : Real.sqrt gammaZero ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by norm_num [gammaZero]))
  field_simp

end
end ASDExplicitGamma.Scalar
