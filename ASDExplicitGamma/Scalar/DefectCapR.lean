module

public import ASDExplicitGamma.Scalar.NewResolventDefectFormula
public import ASDExplicitGamma.Scalar.RefFinalRR
public import ASDExplicitGamma.Scalar.RefRough9
public import ASDExplicitGamma.Numerics.Scalar.LowerR

/-! Identification of the closed-form R-defect `defectFdefR` at the certified constants with the
numerical tree `quarticDefectRExpr`. -/

@[expose] public section
namespace ASDExplicitGamma.Scalar

open ASDExplicitGamma.Numerics.Scalar
open ASDExplicitGamma.Numerics.Mirror

noncomputable section

theorem rough_R_eq_certificate :
    roughR = evalReal scalarRealEnv quarticRoughRExpr := by
  simp only [roughR, quarticRoughRExpr, defect_A_eq_certificate, evalReal, sc]
  push_cast
  ring

theorem defect_fdefR_eq_certificate :
    defectFdefR (evalReal scalarRealEnv lowerA5Expr) (evalReal scalarRealEnv lowerXiExpr)
        (evalReal scalarRealEnv lowerMExpr) (14103 / 10000) (5 / 10 ^ 24)
        (14103 / 10000) (5 / 10 ^ 24) roughR =
      evalReal scalarRealEnv quarticDefectRExpr := by
  simp only [defectFdefR, defectLambda, consumerL, gapEps, graW, eraW,
    defect_A_eq_certificate, defect_delta_eq_certificate, rough_R_eq_certificate]
  simp [quarticDefectRExpr, quarticLambdaExpr, quarticLExpr, quarticGapExpr, quarticGrawExpr,
    quarticErawExpr, quarticEbarExpr, quarticPPExpr, quarticRRExpr, quarticRDExpr,
    evalReal, sc]
  ring_nf

end
end ASDExplicitGamma.Scalar
