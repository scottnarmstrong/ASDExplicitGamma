module

public import ASDExplicitGamma.Numerics.Scalar.Mirror

/-! The coercivity-and-factor formulas and the chaining-row formulas.
The fractional powers of three are written as equivalent nested positive square roots.
-/

@[expose] public section

namespace ASDExplicitGamma.Numerics.Scalar

open Mirror

local infixl:65 " +ₑ " => Expr.add
local infixl:65 " -ₑ " => Expr.sub
local infixl:70 " *ₑ " => Expr.mul
local infixl:70 " /ₑ " => Expr.divPos
local prefix:max "√ₑ " => Expr.sqrt

def sc (q : ℚ) : Expr := .const q
def piExpr : Expr := .var 0
def sqrtThreeExpr : Expr := √ₑ (sc 3)
def fourthThreeExpr : Expr := √ₑ sqrtThreeExpr
def alphaExpr : Expr := sc 1 /ₑ fourthThreeExpr
def piSquareExpr : Expr := piExpr *ₑ piExpr

/-- LOWER_PROOF §4: the compatible coercivity coefficient. -/
def cZeroExpr : Expr :=
  √ₑ (sc 8 *ₑ sqrtThreeExpr /ₑ (sc 9 -ₑ sqrtThreeExpr)) /ₑ piExpr
/-- Here `3^(-3/2) = sqrt 3 / 9`. -/
def cZeroPrimeExpr : Expr :=
  √ₑ (sqrtThreeExpr /ₑ (piSquareExpr *ₑ (sc 1 -ₑ sqrtThreeExpr /ₑ sc 9)))
def cOneExpr : Expr :=
  √ₑ ((sqrtThreeExpr -ₑ sc 1) /ₑ
    (piSquareExpr *ₑ (sc 1 -ₑ sqrtThreeExpr /ₑ sc 9)))
def largeCOneExpr : Expr := cOneExpr +ₑ sc 2 /ₑ piExpr +ₑ sc (1/2)
def fSevenDerivativeExpr : Expr := sc 2 /ₑ piExpr *ₑ √ₑ (sc (78/5))
def fSevenProductExpr : Expr :=
  cZeroExpr *ₑ cOneExpr *ₑ √ₑ (sc (23244/25))
def fSevenFrameExpr : Expr := sc 1 /ₑ sqrtThreeExpr +ₑ largeCOneExpr

theorem f7_coercivity_kernel_check :
    scalarUpperCheck cZeroPrimeExpr (467/1000) = true ∧
    scalarUpperCheck fSevenDerivativeExpr (503/200) = true ∧
    scalarUpperCheck fSevenProductExpr (2031/500) = true ∧
    scalarUpperCheck fSevenFrameExpr (1009/500) = true ∧
    scalarUpperCheck (sc 1 /ₑ piExpr) (319/1000) = true ∧
    scalarUpperCheck (sc 1 +ₑ alphaExpr) (44/25) = true ∧
    scalarUpperCheck (sc (1/2) +ₑ alphaExpr) (63/50) = true := by
  decide +kernel

/-- The coercivity bounds, with strict outward comparisons for all seven constants. -/
theorem f7_coercivity :
    evalReal scalarRealEnv cZeroPrimeExpr < (467/1000 : ℝ) ∧
    evalReal scalarRealEnv fSevenDerivativeExpr < (503/200 : ℝ) ∧
    evalReal scalarRealEnv fSevenProductExpr < (2031/500 : ℝ) ∧
    evalReal scalarRealEnv fSevenFrameExpr < (1009/500 : ℝ) ∧
    evalReal scalarRealEnv (sc 1 /ₑ piExpr) < (319/1000 : ℝ) ∧
    evalReal scalarRealEnv (sc 1 +ₑ alphaExpr) < (44/25 : ℝ) ∧
    evalReal scalarRealEnv (sc (1/2) +ₑ alphaExpr) < (63/50 : ℝ) := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6⟩ := f7_coercivity_kernel_check
  exact ⟨by simpa using scalar_upper_sound _ _ h0,
    by simpa using scalar_upper_sound _ _ h1,
    by simpa using scalar_upper_sound _ _ h2,
    by simpa using scalar_upper_sound _ _ h3,
    by simpa using scalar_upper_sound _ _ h4,
    by simpa using scalar_upper_sound _ _ h5,
    by simpa using scalar_upper_sound _ _ h6⟩

/-- The joint-disk pure factor from LOWER_PROOF §§4–5. -/
def pureFactorExpr : Expr :=
  let a2 := alphaExpr *ₑ alphaExpr
  √ₑ (a2 +ₑ sc (1/2) +ₑ √ₑ (sc (1/4) +ₑ a2))
/-- Six successive positive square roots give the 64th root. -/
def mixedFactorExpr : Expr := √ₑ (√ₑ (√ₑ (√ₑ (√ₑ (√ₑ (sc 1 +ₑ √ₑ (sc 15)))))))
def flatFactorExpr : Expr := sc (3/2) +ₑ sc ((467/1000)^2*(936/5)/729)

theorem f7_factors_kernel_check :
    scalarUpperCheck pureFactorExpr (141/100) = true ∧
    scalarUpperCheck mixedFactorExpr (513/500) = true ∧
    scalarUpperCheck flatFactorExpr (1557/1000) = true := by
  decide +kernel

/-- The three pure/mixed factors. -/
theorem f7_factors :
    evalReal scalarRealEnv pureFactorExpr < (141/100 : ℝ) ∧
    evalReal scalarRealEnv mixedFactorExpr < (513/500 : ℝ) ∧
    evalReal scalarRealEnv flatFactorExpr < (1557/1000 : ℝ) := by
  obtain ⟨h0,h1,h2⟩ := f7_factors_kernel_check
  exact ⟨by simpa using scalar_upper_sound _ _ h0,
    by simpa using scalar_upper_sound _ _ h1,
    by simpa using scalar_upper_sound _ _ h2⟩

/-- CP/born_gaussian_derivative_depth_refinement.md (2)–(4). -/
def fEightRowExpr : Expr :=
  let a1 := √ₑ (sc (12*(312/5))) +ₑ sc 2 *ₑ √ₑ (sc (2*(312/5)))
  let a2 := sc (3/2) *ₑ √ₑ (sc (12*(141648/25))) +ₑ
    sc 6 *ₑ √ₑ (sc (2*(141648/25)))
  let a3 := sc (1/2) *ₑ √ₑ (sc (12*(90462528/125))) +ₑ
    sc 4 *ₑ √ₑ (sc (2*(90462528/125)))
  a1 +ₑ a2 /ₑ sc 81 +ₑ a3 /ₑ sc 6561

theorem f8_row_kernel_check : scalarUpperCheck fEightRowExpr 64 = true := by
  decide +kernel

/-- Retain the complete six-radical chaining formula. -/
theorem f8_row : evalReal scalarRealEnv fEightRowExpr < 64 :=
  scalar_upper_sound _ _ f8_row_kernel_check

/-- CP/born_gaussian_residual_depth_refinement.md (2), since `3^(-7/4)=3^(1/4)/9`. -/
def poincareExpr : Expr :=
  fourthThreeExpr /ₑ (piSquareExpr *ₑ (sc 1 -ₑ fourthThreeExpr /ₑ sc 9))
def residualGeometryExpr : Expr := sqrtThreeExpr *ₑ poincareExpr *ₑ sc (156/5)

theorem f8_geometry_kernel_check :
    scalarUpperCheck poincareExpr (8/45) = true ∧
    scalarUpperCheck residualGeometryExpr (728/75) = true ∧
    (728/75 : ℚ) < 10 ∧ (7 : ℕ)^5 < 3^9 := by
  decide +kernel

/-- Both positive-norm geometry comparisons. -/
theorem f8_geometry :
    evalReal scalarRealEnv poincareExpr < (8/45 : ℝ) ∧
    evalReal scalarRealEnv residualGeometryExpr < (728/75 : ℝ) ∧
    (728/75 : ℝ) < 10 ∧ (7 : ℕ)^5 < 3^9 := by
  obtain ⟨hp,hr,_hn,hi⟩ := f8_geometry_kernel_check
  exact ⟨by simpa using scalar_upper_sound _ _ hp,
    by simpa using scalar_upper_sound _ _ hr, by norm_num, hi⟩

end ASDExplicitGamma.Numerics.Scalar
