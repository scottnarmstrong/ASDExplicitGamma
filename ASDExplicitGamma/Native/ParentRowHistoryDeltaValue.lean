module

public import ASDExplicitGamma.Native.ParentRowHistoryDeltaFields

/-! Readable real interpretation of the five-degree parent history drift. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native Numerics.Mirror
noncomputable section

/-- Polynomial coefficients before the two literal geometric payments. -/
def parentRowHistoryPolynomial (a2 a4 : ℝ) : Fin 5 → ℝ :=
  let a := Real.sqrt (a2*(39/5))
  let b := Real.sqrt (a2*(156/5))*(36/25)
  let c := Real.sqrt (a4*(46488/25))*(57/200)
  let d := Real.sqrt (a2*(78/5))*(36/25)
  let e := Real.sqrt (a4*(23244/25))*(57/200)
  ![(232/125)*a^2+38*a^2, 2*(232/125)*a*b+76*a*d,
    (232/125)*(b^2+2*a*c)+38*(d^2+2*a*e),
    2*(232/125)*b*c+76*d*e, (232/125)*c^2+38*e^2]

/-- The exact source drift with five degrees and both physical growth ratios. -/
def parentRowHistoryDeltaValue (height : ℕ) : ℝ :=
  let v := parentRowVarianceClock height
  let a2 := parentRowWeightedClock parentRowA2Weight height
  let a4 := parentRowWeightedClock parentRowA4Weight height
  let f := Real.exp (Real.log 3*((17/50000)*(2*(height:ℝ)+24)))*4
  let q := fun (g : ℝ) (i : Fin 5) =>
    (1/Real.exp (Real.log 3*(3/20)))*Real.exp (Real.log 3*g)*(1/3:ℝ)^i.val
  ∑ i : Fin 5,(1-1/Real.sqrt (Real.sqrt 3))*parentRowHistoryPolynomial a2 a4 i*
    (f*(176338357/78125000)*
        ((parentRowRawBase height:ℝ)/(1-q (17/6250) i)+
          (q (17/6250) i*(276029/25000))/(1-q (17/6250) i)^2)+
      v*1248*(49958012987/15625000000)/(1-q (51/25000) i))

/-- Interpretation of the kernel-checked drift expression is the literal
real polynomial/geometric formula, before any inequality is applied. -/
theorem parent_row_history_delta_expr_eval (env : ℕ → ℝ)
    (hlog : env 2=Real.log 3) (height : ℕ) :
    evalReal env (parentRowHistoryDeltaExpr height)=parentRowHistoryDeltaValue height := by
  simp only [parentRowHistoryDeltaExpr,evalReal,
    parent_row_variance_expr_eval env hlog,parent_row_weighted_expr_eval env hlog,
    hlog,parentRowHistoryDeltaValue,Fin.sum_univ_succ,Fin.sum_univ_zero,
    Fin.val_zero,Fin.val_succ,parentRowHistoryPolynomial,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Rat.cast_div,Rat.cast_mul,Rat.cast_add,Rat.cast_natCast,Rat.cast_ofNat,Rat.cast_zero,
    Rat.cast_one,div_one,zero_add,one_mul,pow_zero,mul_one]
  norm_num only [Nat.reduceAdd, pow_succ]
  ring

end
end ASDExplicitGamma.Native
