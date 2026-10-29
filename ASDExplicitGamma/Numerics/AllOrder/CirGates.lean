module

public import ASDExplicitGamma.Numerics.Scalar.Factors

/-! NU-AO-CIR-GATES, exact constants.
The full bracket retains the extra factor four supplied by Lemma V.
-/

@[expose] public section
namespace ASDExplicitGamma.Numerics.AllOrder
open Mirror Scalar
local infixl:65 " +ₑ " => Expr.add
local infixl:70 " *ₑ " => Expr.mul
local infixl:70 " /ₑ " => Expr.divPos
local prefix:max "√ₑ " => Expr.sqrt

def cirAExpr : Expr := sc 1.860 +ₑ sc (2.36412/243) *ₑ √ₑ (sc (156/5)) +ₑ
  sc (0.52288/243^2) *ₑ √ₑ (sc (46488/25))
def cirBExpr : Expr := sc 1.860 +ₑ sc (2.36412/243) *ₑ √ₑ (sc (78/5)) +ₑ
  sc (0.52288/243^2) *ₑ √ₑ (sc (23244/25))
def cirFeedbackExpr : Expr := sc 2.265 +ₑ √ₑ (sc 2.265)
def cirPowerExpr : Expr := .exp (sc (16/327680) *ₑ .var 1)
def cirContractionExpr : Expr :=
  sc 1.017 *ₑ (sc (700/(12*900000)) +ₑ
    sc 144 *ₑ (sc (3/3^8) /ₑ √ₑ (sc 12) +ₑ sc (9/3^16)) +ₑ
    sc ((107/12)*(9/2)*8*(2.2)^2*50/900000) *ₑ cirPowerExpr) +ₑ
  sc (1/(12*900000))

theorem cir_kernel_check :
    scalarUpperCheck (√ₑ (sc (156/5))) 5.586 = true ∧
    scalarUpperCheck (√ₑ (sc (46488/25))) 43.123 = true ∧
    scalarUpperCheck (√ₑ (sc (78/5))) 3.950 = true ∧
    scalarUpperCheck (√ₑ (sc (23244/25))) 30.493 = true ∧
    scalarUpperCheck (√ₑ (sc 2.265)) 1.506 = true ∧
    scalarUpperCheck cirAExpr 1.915 = true ∧ scalarUpperCheck cirBExpr 1.899 = true ∧
    scalarUpperCheck cirFeedbackExpr 3.771 = true ∧ scalarUpperCheck cirPowerExpr (1001/1000) = true ∧
    scalarUpperCheck cirContractionExpr (14/100) = true := by
  decide +kernel

theorem cir_principal_minors :
    (1.899 : ℚ)^2 = 3.606201 ∧ (3.606201 : ℚ) < 4 ∧
    (19-2.265*1.915^2 : ℚ) > 0 ∧
    (19*(19-2.265*1.915^2)-3.771^2*1.915^2*1.899^2 : ℚ) > 15 ∧
    (15 : ℚ) > 0 ∧ (4*4 : ℚ) = 16 ∧ (9*16 : ℚ) = 144 ∧
    (3.46 : ℚ)^2 < 12 ∧ (14/100 : ℚ) < 1 := by
  decide +kernel

/-- Source transport coefficients at the largest permitted geometric ratio. -/
theorem cir_coefficient_caps :
    (1.860+(2.36412/243)*Real.sqrt (156/5)+(0.52288/243^2)*Real.sqrt (46488/25) : ℝ) < 1.915 ∧
    (1.860+(2.36412/243)*Real.sqrt (78/5)+(0.52288/243^2)*Real.sqrt (23244/25) : ℝ) < 1.899 ∧
    (2.265+Real.sqrt 2.265 : ℝ) < 3.771 := by
  have h := cir_kernel_check
  have ha := scalar_upper_sound _ _ h.2.2.2.2.2.1
  have hb := scalar_upper_sound _ _ h.2.2.2.2.2.2.1
  have hd := scalar_upper_sound _ _ h.2.2.2.2.2.2.2.1
  norm_num [cirAExpr, cirBExpr, cirFeedbackExpr, sc, evalReal] at ha hb hd ⊢
  exact ⟨ha,hb,hd⟩

/-- The genuine finite-even contraction, using the true exponential and sqrt(12). -/
theorem cir_contraction :
    (1.017 : ℝ)*((700/(12*900000))+
      144*((3/(3^8*Real.sqrt 12))+(9/3^16))+
      (107/12)*(9/2)*8*(2.2)^2*50*(3 : ℝ)^(16/327680 : ℝ)/900000)+
      1/(12*900000) < 14/100 := by
  have h := scalar_upper_sound _ _ cir_kernel_check.2.2.2.2.2.2.2.2.2
  norm_num [cirContractionExpr, cirPowerExpr, sc, evalReal, scalarRealEnv] at h
  rw [Real.rpow_def_of_pos (by norm_num)]
  norm_num at ⊢
  convert h using 1
  ring

/-- The two source generator allocations for arbitrary real order. -/
theorem cir_order_allocations (p : ℝ) :
    (12 ≤ p → 19+8*(p-1) ≤ (107/12)*p) ∧
    (1 ≤ p → 19+8*(p-1) ≤ 19*p) := by
  constructor <;> intro hp <;> linarith only [hp]

end ASDExplicitGamma.Numerics.AllOrder
