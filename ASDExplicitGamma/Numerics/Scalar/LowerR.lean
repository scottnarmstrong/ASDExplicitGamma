module

public import ASDExplicitGamma.Numerics.Scalar.Lower

/-! The certified scalar tree in which the rough constant `quarticRoughOldExpr`
is replaced by `R = A²((44/25)β+1)⁴`, `β = 14103/10000`; nothing else changes. -/

@[expose] public section
namespace ASDExplicitGamma.Numerics.Scalar
open Mirror
local infixl:65 " +ₑ " => Expr.add
local infixl:65 " -ₑ " => Expr.sub
local infixl:70 " *ₑ " => Expr.mul
local infixl:70 " /ₑ " => Expr.divPos
local prefix:max "√ₑ " => Expr.sqrt

/-- `R = A²((44/25)β+1)⁴`. -/
def quarticRoughRExpr : Expr :=
  (lowerAExpr *ₑ lowerAExpr) *ₑ
    (((sc (44/25) *ₑ sc (14103/10000)) +ₑ sc (1/1)) *ₑ
      (((sc (44/25) *ₑ sc (14103/10000)) +ₑ sc (1/1)) *ₑ
        (((sc (44/25) *ₑ sc (14103/10000)) +ₑ sc (1/1)) *ₑ
          ((sc (44/25) *ₑ sc (14103/10000)) +ₑ sc (1/1)))))

def quarticDefectRExpr : Expr := (((lowerAExpr *ₑ lowerAExpr) *ₑ sc (3/1)) *ₑ ((sc (14103/10000) *ₑ quarticLambdaExpr) +ₑ ((sc (1/200000000000000000000000) *ₑ sc (513/500)) *ₑ quarticRoughRExpr)))

def quarticSharpRExpr : Expr := ((quarticFlatExpr +ₑ ((√ₑ ((quarticFlatExpr *ₑ quarticDefectRExpr))) *ₑ sc (141/50))) +ₑ (sc (44/25) *ₑ quarticDefectRExpr))

def quarticChargeRExpr : Expr := ((quarticSharpRExpr *ₑ sc (187/250000)) /ₑ sc (249813/250000))

def lowerGainRExpr : Expr := (lowerBaseExpr -ₑ (quarticChargeRExpr /ₑ sc (31/50)))

theorem lower_gain_R_kernel_check :
    scalarUpperCheck (.neg lowerGainRExpr) (-(3143488/10^7)) = true := by
  decide +kernel

theorem lower_gain_margin_R :
    (3143488/10^7 : ℝ) ≤ evalReal scalarRealEnv lowerGainRExpr ∧
    (12493/40000 : ℝ) < 3143488/10^7 ∧
    (12493/40000 : ℝ) = (31/50)*((1+3*(1/200)/2)/2) := by
  have h := scalar_upper_sound _ _ lower_gain_R_kernel_check
  change -evalReal scalarRealEnv lowerGainRExpr < _ at h
  norm_num at h
  refine ⟨?_, by norm_num, by norm_num⟩
  linarith only [h]

end ASDExplicitGamma.Numerics.Scalar
