module

public import ASDExplicitGamma.Numerics.Scalar.Factors
import Mathlib.Tactic.IntervalCases

/-! Generated data (exact rationals), checked by kernel reduction.
No source producer is imported or executed. Every arithmetic tree has its real interpretation
and is evaluated by the sound grid mirror. -/

@[expose] public section
namespace ASDExplicitGamma.Numerics.Scalar
open Mirror
local infixl:65 " +ₑ " => Expr.add
local infixl:65 " -ₑ " => Expr.sub
local infixl:70 " *ₑ " => Expr.mul
local infixl:70 " /ₑ " => Expr.divPos
local prefix:max "√ₑ " => Expr.sqrt

def upperSafeSourceExpr : Expr := sc (13276004954337698463246677797499/100000000000000000000000000000000)

def upperMExpr : Expr := ((√ₑ (sc (61/5))) +ₑ sc (66/5))

def upperMnewExpr : Expr := (sc (4401220936909581/125000000000) *ₑ (sc (1/1) /ₑ sc (5739/25000)))

def upperFExpr : Expr := (((√ₑ (sc (17/50000))) *ₑ sc (64/1)) /ₑ sc (4782969/1))

def upperSensitivityExpr : Expr := (((upperMExpr *ₑ sc (24/1)) *ₑ upperMExpr) *ₑ ((upperFExpr +ₑ ((upperFExpr *ₑ sc (2/1)) *ₑ upperFExpr)) +ₑ ((upperFExpr *ₑ (upperFExpr *ₑ upperFExpr)) *ₑ sc (4/1))))

def upperResidualExpr : Expr := (((upperMnewExpr *ₑ sc (10/1)) *ₑ sc (17/50000)) /ₑ sc (22876792454961/1))

def upperErrorExpr : Expr := (((((upperSafeSourceExpr /ₑ sc (2/1)) +ₑ upperSensitivityExpr) +ₑ ((√ₑ ((upperResidualExpr *ₑ sc (2/1)))) *ₑ sc (2/1))) +ₑ upperResidualExpr) +ₑ sc (17/285959905687012500))

def upperPrincipalExpr : Expr := ((((upperSafeSourceExpr /ₑ sc (2/1)) +ₑ sc (19/10)) +ₑ upperSensitivityExpr) +ₑ sc (17/285959905687012500))


/-- NU-SC-UPPER-ERROR: includes the unpatched safe source allowance. -/
theorem upper_error_kernel_check :
    scalarUpperCheck upperErrorExpr (681/10000) = true ∧
    scalarUpperCheck upperPrincipalExpr 2 = true ∧
    scalarUpperCheck upperFExpr 1 = true ∧
    scalarUpperCheck (sc 1 +ₑ sqrtThreeExpr *ₑ sc (9/10)) 4 = true := by
  decide +kernel

theorem upper_error_bounds :
    evalReal scalarRealEnv upperErrorExpr < (681/10000 : ℝ) ∧
    evalReal scalarRealEnv upperPrincipalExpr < 2 ∧
    evalReal scalarRealEnv upperFExpr < 1 ∧
    evalReal scalarRealEnv (sc 1 +ₑ sqrtThreeExpr *ₑ sc (9/10)) < 4 := by
  obtain ⟨he,hp,hf,hg⟩ := upper_error_kernel_check
  exact ⟨by simpa using scalar_upper_sound _ _ he,
    by simpa using scalar_upper_sound _ _ hp, by simpa using scalar_upper_sound _ _ hf, by simpa using scalar_upper_sound _ _ hg⟩
end ASDExplicitGamma.Numerics.Scalar
