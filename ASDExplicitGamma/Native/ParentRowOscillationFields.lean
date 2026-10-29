module

public import ASDExplicitGamma.Native.ParentRowWeightedFields

/-! Exact root oscillation fields in all sixteen parent source programs. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native Numerics.Mirror
noncomputable section

/-- Literal source expression for either sign of the oscillation coefficient. -/
def parentRowOscillationExpr (height : ℕ) (plus : Bool) : Expr :=
  let root := Expr.sqrt (.mul (parentRowWeightedExpr parentRowA2Weight height) (.const (156/5)))
  if plus then .mul (.mul (.add (.sqrt (.const 2)) (.const 1)) (.const (11/25))) root
  else .mul root (.const (11/25))

/-- Readable common oscillation coefficient. -/
def parentRowOscillationValue (height : ℕ) (plus : Bool) : ℝ :=
  ((if plus then 1+Real.sqrt 2 else 1)*(11/25))*
    Real.sqrt (parentRowWeightedClock parentRowA2Weight height*(156/5))

/-- Exact real interpretation of the two source expressions. -/
theorem parent_row_oscillation_expr_eval (env : ℕ → ℝ)
    (hlog : env 2=Real.log 3) (height : ℕ) (plus : Bool) :
    evalReal env (parentRowOscillationExpr height plus)=parentRowOscillationValue height plus := by
  cases plus <;> simp only [parentRowOscillationExpr,parentRowOscillationValue,
    Bool.false_eq_true,ite_false,ite_true,evalReal,
    parent_row_weighted_expr_eval env hlog,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] <;> ring

/-- Exact plus oscillation at height 1. -/
theorem parent_row_oscillation_plus_001 :
    nativeSetupParent001FieldsR.getD 4 0=parentRowOscillationValue 1 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent001A0 nativeSetupParent001Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent001A0 nativeSetupParent001Xi0 := by rfl
  have hl : (nativeSetupParent001Ops.drop 64).length=381 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent001Ops.take 64)).getD 0 (.const 0)=parentRowOscillationExpr 1 true := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent001Ops.take 64) (nativeSetupParent001Ops.drop 64) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_oscillation_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent001FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent001Real] using hh

/-- Exact minus oscillation at height 1. -/
theorem parent_row_oscillation_minus_001 :
    nativeSetupParent001FieldsR.getD 5 0=parentRowOscillationValue 1 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent001A0 nativeSetupParent001Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent001A0 nativeSetupParent001Xi0 := by rfl
  have hl : (nativeSetupParent001Ops.drop 65).length=380 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent001Ops.take 65)).getD 0 (.const 0)=parentRowOscillationExpr 1 false := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent001Ops.take 65) (nativeSetupParent001Ops.drop 65) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_oscillation_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent001FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent001Real] using hh

/-- Exact plus oscillation at height 2. -/
theorem parent_row_oscillation_plus_002 :
    nativeSetupParent002FieldsR.getD 4 0=parentRowOscillationValue 2 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent002A0 nativeSetupParent002Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent002A0 nativeSetupParent002Xi0 := by rfl
  have hl : (nativeSetupParent002Ops.drop 75).length=398 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent002Ops.take 75)).getD 0 (.const 0)=parentRowOscillationExpr 2 true := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent002Ops.take 75) (nativeSetupParent002Ops.drop 75) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_oscillation_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent002FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent002Real] using hh

/-- Exact minus oscillation at height 2. -/
theorem parent_row_oscillation_minus_002 :
    nativeSetupParent002FieldsR.getD 5 0=parentRowOscillationValue 2 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent002A0 nativeSetupParent002Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent002A0 nativeSetupParent002Xi0 := by rfl
  have hl : (nativeSetupParent002Ops.drop 76).length=397 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent002Ops.take 76)).getD 0 (.const 0)=parentRowOscillationExpr 2 false := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent002Ops.take 76) (nativeSetupParent002Ops.drop 76) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_oscillation_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent002FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent002Real] using hh

/-- Exact plus oscillation at height 3. -/
theorem parent_row_oscillation_plus_003 :
    nativeSetupParent003FieldsR.getD 4 0=parentRowOscillationValue 3 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent003A0 nativeSetupParent003Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent003A0 nativeSetupParent003Xi0 := by rfl
  have hl : (nativeSetupParent003Ops.drop 86).length=415 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent003Ops.take 86)).getD 0 (.const 0)=parentRowOscillationExpr 3 true := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent003Ops.take 86) (nativeSetupParent003Ops.drop 86) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_oscillation_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent003FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent003Real] using hh

/-- Exact minus oscillation at height 3. -/
theorem parent_row_oscillation_minus_003 :
    nativeSetupParent003FieldsR.getD 5 0=parentRowOscillationValue 3 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent003A0 nativeSetupParent003Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent003A0 nativeSetupParent003Xi0 := by rfl
  have hl : (nativeSetupParent003Ops.drop 87).length=414 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent003Ops.take 87)).getD 0 (.const 0)=parentRowOscillationExpr 3 false := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent003Ops.take 87) (nativeSetupParent003Ops.drop 87) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_oscillation_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent003FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent003Real] using hh

/-- Exact plus oscillation at height 4. -/
theorem parent_row_oscillation_plus_004 :
    nativeSetupParent004FieldsR.getD 4 0=parentRowOscillationValue 4 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent004A0 nativeSetupParent004Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent004A0 nativeSetupParent004Xi0 := by rfl
  have hl : (nativeSetupParent004Ops.drop 97).length=432 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent004Ops.take 97)).getD 0 (.const 0)=parentRowOscillationExpr 4 true := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent004Ops.take 97) (nativeSetupParent004Ops.drop 97) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_oscillation_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent004FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent004Real] using hh

/-- Exact minus oscillation at height 4. -/
theorem parent_row_oscillation_minus_004 :
    nativeSetupParent004FieldsR.getD 5 0=parentRowOscillationValue 4 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent004A0 nativeSetupParent004Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent004A0 nativeSetupParent004Xi0 := by rfl
  have hl : (nativeSetupParent004Ops.drop 98).length=431 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent004Ops.take 98)).getD 0 (.const 0)=parentRowOscillationExpr 4 false := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent004Ops.take 98) (nativeSetupParent004Ops.drop 98) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_oscillation_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent004FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent004Real] using hh

/-- Exact plus oscillation at height 5. -/
theorem parent_row_oscillation_plus_005 :
    nativeSetupParent005FieldsR.getD 4 0=parentRowOscillationValue 5 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent005A0 nativeSetupParent005Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent005A0 nativeSetupParent005Xi0 := by rfl
  have hl : (nativeSetupParent005Ops.drop 108).length=449 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent005Ops.take 108)).getD 0 (.const 0)=parentRowOscillationExpr 5 true := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent005Ops.take 108) (nativeSetupParent005Ops.drop 108) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_oscillation_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent005FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent005Real] using hh

/-- Exact minus oscillation at height 5. -/
theorem parent_row_oscillation_minus_005 :
    nativeSetupParent005FieldsR.getD 5 0=parentRowOscillationValue 5 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent005A0 nativeSetupParent005Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent005A0 nativeSetupParent005Xi0 := by rfl
  have hl : (nativeSetupParent005Ops.drop 109).length=448 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent005Ops.take 109)).getD 0 (.const 0)=parentRowOscillationExpr 5 false := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent005Ops.take 109) (nativeSetupParent005Ops.drop 109) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_oscillation_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent005FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent005Real] using hh

/-- Exact plus oscillation at height 6. -/
theorem parent_row_oscillation_plus_006 :
    nativeSetupParent006FieldsR.getD 4 0=parentRowOscillationValue 6 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent006A0 nativeSetupParent006Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent006A0 nativeSetupParent006Xi0 := by rfl
  have hl : (nativeSetupParent006Ops.drop 119).length=469 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent006Ops.take 119)).getD 0 (.const 0)=parentRowOscillationExpr 6 true := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent006Ops.take 119) (nativeSetupParent006Ops.drop 119) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_oscillation_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent006FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent006Real] using hh

/-- Exact minus oscillation at height 6. -/
theorem parent_row_oscillation_minus_006 :
    nativeSetupParent006FieldsR.getD 5 0=parentRowOscillationValue 6 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent006A0 nativeSetupParent006Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent006A0 nativeSetupParent006Xi0 := by rfl
  have hl : (nativeSetupParent006Ops.drop 120).length=468 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent006Ops.take 120)).getD 0 (.const 0)=parentRowOscillationExpr 6 false := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent006Ops.take 120) (nativeSetupParent006Ops.drop 120) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_oscillation_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent006FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent006Real] using hh

/-- Exact plus oscillation at height 7. -/
theorem parent_row_oscillation_plus_007 :
    nativeSetupParent007FieldsR.getD 4 0=parentRowOscillationValue 7 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent007A0 nativeSetupParent007Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent007A0 nativeSetupParent007Xi0 := by rfl
  have hl : (nativeSetupParent007Ops.drop 129).length=489 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent007Ops.take 129)).getD 0 (.const 0)=parentRowOscillationExpr 7 true := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent007Ops.take 129) (nativeSetupParent007Ops.drop 129) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_oscillation_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent007FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent007Real] using hh

/-- Exact minus oscillation at height 7. -/
theorem parent_row_oscillation_minus_007 :
    nativeSetupParent007FieldsR.getD 5 0=parentRowOscillationValue 7 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent007A0 nativeSetupParent007Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent007A0 nativeSetupParent007Xi0 := by rfl
  have hl : (nativeSetupParent007Ops.drop 130).length=488 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent007Ops.take 130)).getD 0 (.const 0)=parentRowOscillationExpr 7 false := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent007Ops.take 130) (nativeSetupParent007Ops.drop 130) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_oscillation_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent007FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent007Real] using hh

/-- Exact plus oscillation at height 8. -/
theorem parent_row_oscillation_plus_008 :
    nativeSetupParent008FieldsR.getD 4 0=parentRowOscillationValue 8 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent008A0 nativeSetupParent008Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent008A0 nativeSetupParent008Xi0 := by rfl
  have hl : (nativeSetupParent008Ops.drop 140).length=509 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent008Ops.take 140)).getD 0 (.const 0)=parentRowOscillationExpr 8 true := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent008Ops.take 140) (nativeSetupParent008Ops.drop 140) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_oscillation_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent008FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent008Real] using hh

/-- Exact minus oscillation at height 8. -/
theorem parent_row_oscillation_minus_008 :
    nativeSetupParent008FieldsR.getD 5 0=parentRowOscillationValue 8 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent008A0 nativeSetupParent008Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent008A0 nativeSetupParent008Xi0 := by rfl
  have hl : (nativeSetupParent008Ops.drop 141).length=508 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent008Ops.take 141)).getD 0 (.const 0)=parentRowOscillationExpr 8 false := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent008Ops.take 141) (nativeSetupParent008Ops.drop 141) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_oscillation_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent008FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent008Real] using hh

/-- Exact plus oscillation at height 9. -/
theorem parent_row_oscillation_plus_009 :
    nativeSetupParent009FieldsR.getD 4 0=parentRowOscillationValue 9 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent009A0 nativeSetupParent009Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent009A0 nativeSetupParent009Xi0 := by rfl
  have hl : (nativeSetupParent009Ops.drop 150).length=529 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent009Ops.take 150)).getD 0 (.const 0)=parentRowOscillationExpr 9 true := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent009Ops.take 150) (nativeSetupParent009Ops.drop 150) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_oscillation_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent009FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent009Real] using hh

/-- Exact minus oscillation at height 9. -/
theorem parent_row_oscillation_minus_009 :
    nativeSetupParent009FieldsR.getD 5 0=parentRowOscillationValue 9 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent009A0 nativeSetupParent009Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent009A0 nativeSetupParent009Xi0 := by rfl
  have hl : (nativeSetupParent009Ops.drop 151).length=528 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent009Ops.take 151)).getD 0 (.const 0)=parentRowOscillationExpr 9 false := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent009Ops.take 151) (nativeSetupParent009Ops.drop 151) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_oscillation_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent009FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent009Real] using hh

/-- Exact plus oscillation at height 10. -/
theorem parent_row_oscillation_plus_010 :
    nativeSetupParent010FieldsR.getD 4 0=parentRowOscillationValue 10 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent010A0 nativeSetupParent010Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent010A0 nativeSetupParent010Xi0 := by rfl
  have hl : (nativeSetupParent010Ops.drop 161).length=549 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent010Ops.take 161)).getD 0 (.const 0)=parentRowOscillationExpr 10 true := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent010Ops.take 161) (nativeSetupParent010Ops.drop 161) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_oscillation_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent010FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent010Real] using hh

/-- Exact minus oscillation at height 10. -/
theorem parent_row_oscillation_minus_010 :
    nativeSetupParent010FieldsR.getD 5 0=parentRowOscillationValue 10 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent010A0 nativeSetupParent010Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent010A0 nativeSetupParent010Xi0 := by rfl
  have hl : (nativeSetupParent010Ops.drop 162).length=548 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent010Ops.take 162)).getD 0 (.const 0)=parentRowOscillationExpr 10 false := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent010Ops.take 162) (nativeSetupParent010Ops.drop 162) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_oscillation_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent010FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent010Real] using hh

/-- Exact plus oscillation at height 11. -/
theorem parent_row_oscillation_plus_011 :
    nativeSetupParent011FieldsR.getD 4 0=parentRowOscillationValue 11 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent011A0 nativeSetupParent011Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent011A0 nativeSetupParent011Xi0 := by rfl
  have hl : (nativeSetupParent011Ops.drop 171).length=569 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent011Ops.take 171)).getD 0 (.const 0)=parentRowOscillationExpr 11 true := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent011Ops.take 171) (nativeSetupParent011Ops.drop 171) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_oscillation_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent011FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent011Real] using hh

/-- Exact minus oscillation at height 11. -/
theorem parent_row_oscillation_minus_011 :
    nativeSetupParent011FieldsR.getD 5 0=parentRowOscillationValue 11 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent011A0 nativeSetupParent011Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent011A0 nativeSetupParent011Xi0 := by rfl
  have hl : (nativeSetupParent011Ops.drop 172).length=568 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent011Ops.take 172)).getD 0 (.const 0)=parentRowOscillationExpr 11 false := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent011Ops.take 172) (nativeSetupParent011Ops.drop 172) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_oscillation_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent011FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent011Real] using hh

/-- Exact plus oscillation at height 12. -/
theorem parent_row_oscillation_plus_012 :
    nativeSetupParent012FieldsR.getD 4 0=parentRowOscillationValue 12 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent012A0 nativeSetupParent012Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent012A0 nativeSetupParent012Xi0 := by rfl
  have hl : (nativeSetupParent012Ops.drop 182).length=589 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent012Ops.take 182)).getD 0 (.const 0)=parentRowOscillationExpr 12 true := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent012Ops.take 182) (nativeSetupParent012Ops.drop 182) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_oscillation_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent012FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent012Real] using hh

/-- Exact minus oscillation at height 12. -/
theorem parent_row_oscillation_minus_012 :
    nativeSetupParent012FieldsR.getD 5 0=parentRowOscillationValue 12 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent012A0 nativeSetupParent012Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent012A0 nativeSetupParent012Xi0 := by rfl
  have hl : (nativeSetupParent012Ops.drop 183).length=588 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent012Ops.take 183)).getD 0 (.const 0)=parentRowOscillationExpr 12 false := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent012Ops.take 183) (nativeSetupParent012Ops.drop 183) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_oscillation_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent012FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent012Real] using hh

/-- Exact plus oscillation at height 13. -/
theorem parent_row_oscillation_plus_013 :
    nativeSetupParent013FieldsR.getD 4 0=parentRowOscillationValue 13 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent013A0 nativeSetupParent013Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent013A0 nativeSetupParent013Xi0 := by rfl
  have hl : (nativeSetupParent013Ops.drop 192).length=609 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent013Ops.take 192)).getD 0 (.const 0)=parentRowOscillationExpr 13 true := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent013Ops.take 192) (nativeSetupParent013Ops.drop 192) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_oscillation_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent013FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent013Real] using hh

/-- Exact minus oscillation at height 13. -/
theorem parent_row_oscillation_minus_013 :
    nativeSetupParent013FieldsR.getD 5 0=parentRowOscillationValue 13 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent013A0 nativeSetupParent013Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent013A0 nativeSetupParent013Xi0 := by rfl
  have hl : (nativeSetupParent013Ops.drop 193).length=608 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent013Ops.take 193)).getD 0 (.const 0)=parentRowOscillationExpr 13 false := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent013Ops.take 193) (nativeSetupParent013Ops.drop 193) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_oscillation_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent013FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent013Real] using hh

/-- Exact plus oscillation at height 14. -/
theorem parent_row_oscillation_plus_014 :
    nativeSetupParent014FieldsR.getD 4 0=parentRowOscillationValue 14 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent014A0 nativeSetupParent014Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent014A0 nativeSetupParent014Xi0 := by rfl
  have hl : (nativeSetupParent014Ops.drop 203).length=629 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent014Ops.take 203)).getD 0 (.const 0)=parentRowOscillationExpr 14 true := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent014Ops.take 203) (nativeSetupParent014Ops.drop 203) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_oscillation_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent014FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent014Real] using hh

/-- Exact minus oscillation at height 14. -/
theorem parent_row_oscillation_minus_014 :
    nativeSetupParent014FieldsR.getD 5 0=parentRowOscillationValue 14 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent014A0 nativeSetupParent014Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent014A0 nativeSetupParent014Xi0 := by rfl
  have hl : (nativeSetupParent014Ops.drop 204).length=628 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent014Ops.take 204)).getD 0 (.const 0)=parentRowOscillationExpr 14 false := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent014Ops.take 204) (nativeSetupParent014Ops.drop 204) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_oscillation_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent014FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent014Real] using hh

/-- Exact plus oscillation at height 15. -/
theorem parent_row_oscillation_plus_015 :
    nativeSetupParent015FieldsR.getD 4 0=parentRowOscillationValue 15 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent015A0 nativeSetupParent015Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent015A0 nativeSetupParent015Xi0 := by rfl
  have hl : (nativeSetupParent015Ops.drop 213).length=649 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent015Ops.take 213)).getD 0 (.const 0)=parentRowOscillationExpr 15 true := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent015Ops.take 213) (nativeSetupParent015Ops.drop 213) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_oscillation_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent015FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent015Real] using hh

/-- Exact minus oscillation at height 15. -/
theorem parent_row_oscillation_minus_015 :
    nativeSetupParent015FieldsR.getD 5 0=parentRowOscillationValue 15 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent015A0 nativeSetupParent015Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent015A0 nativeSetupParent015Xi0 := by rfl
  have hl : (nativeSetupParent015Ops.drop 214).length=648 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent015Ops.take 214)).getD 0 (.const 0)=parentRowOscillationExpr 15 false := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent015Ops.take 214) (nativeSetupParent015Ops.drop 214) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_oscillation_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent015FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent015Real] using hh

/-- Exact plus oscillation at height 16. -/
theorem parent_row_oscillation_plus_016 :
    nativeSetupParent016FieldsR.getD 4 0=parentRowOscillationValue 16 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent016A0 nativeSetupParent016Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent016A0 nativeSetupParent016Xi0 := by rfl
  have hl : (nativeSetupParent016Ops.drop 224).length=669 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent016Ops.take 224)).getD 0 (.const 0)=parentRowOscillationExpr 16 true := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent016Ops.take 224) (nativeSetupParent016Ops.drop 224) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_oscillation_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent016FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent016Real] using hh

/-- Exact minus oscillation at height 16. -/
theorem parent_row_oscillation_minus_016 :
    nativeSetupParent016FieldsR.getD 5 0=parentRowOscillationValue 16 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent016A0 nativeSetupParent016Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent016A0 nativeSetupParent016Xi0 := by rfl
  have hl : (nativeSetupParent016Ops.drop 225).length=668 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent016Ops.take 225)).getD 0 (.const 0)=parentRowOscillationExpr 16 false := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent016Ops.take 225) (nativeSetupParent016Ops.drop 225) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_oscillation_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent016FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent016Real] using hh

/-- Both selected oscillation fields are their exact finite-band root clocks. -/
theorem parent_row_oscillation_field (j : Fin 16) (plus : Bool) :
    (parentRowFields j).getD (if plus then 4 else 5) 0=
      parentRowOscillationValue (j.val+1) plus := by
  cases plus
  · fin_cases j <;> simp only [Bool.false_eq_true,ite_false,parentRowFields,
      nativeConfiguredParentEndpoint,nativeParentEndpointCertificates,nativeParent001EndpointCertificate,nativeParent002EndpointCertificate,nativeParent003EndpointCertificate,nativeParent004EndpointCertificate,nativeParent005EndpointCertificate,nativeParent006EndpointCertificate,nativeParent007EndpointCertificate,nativeParent008EndpointCertificate,nativeParent009EndpointCertificate,nativeParent010EndpointCertificate,nativeParent011EndpointCertificate,nativeParent012EndpointCertificate,nativeParent013EndpointCertificate,nativeParent014EndpointCertificate,nativeParent015EndpointCertificate,nativeParent016EndpointCertificate,
      List.getD_cons_zero,List.getD_cons_succ]
    · exact parent_row_oscillation_minus_001
    · exact parent_row_oscillation_minus_002
    · exact parent_row_oscillation_minus_003
    · exact parent_row_oscillation_minus_004
    · exact parent_row_oscillation_minus_005
    · exact parent_row_oscillation_minus_006
    · exact parent_row_oscillation_minus_007
    · exact parent_row_oscillation_minus_008
    · exact parent_row_oscillation_minus_009
    · exact parent_row_oscillation_minus_010
    · exact parent_row_oscillation_minus_011
    · exact parent_row_oscillation_minus_012
    · exact parent_row_oscillation_minus_013
    · exact parent_row_oscillation_minus_014
    · exact parent_row_oscillation_minus_015
    · exact parent_row_oscillation_minus_016
  · fin_cases j <;> simp only [ite_true,parentRowFields,
      nativeConfiguredParentEndpoint,nativeParentEndpointCertificates,nativeParent001EndpointCertificate,nativeParent002EndpointCertificate,nativeParent003EndpointCertificate,nativeParent004EndpointCertificate,nativeParent005EndpointCertificate,nativeParent006EndpointCertificate,nativeParent007EndpointCertificate,nativeParent008EndpointCertificate,nativeParent009EndpointCertificate,nativeParent010EndpointCertificate,nativeParent011EndpointCertificate,nativeParent012EndpointCertificate,nativeParent013EndpointCertificate,nativeParent014EndpointCertificate,nativeParent015EndpointCertificate,nativeParent016EndpointCertificate,
      List.getD_cons_zero,List.getD_cons_succ]
    · exact parent_row_oscillation_plus_001
    · exact parent_row_oscillation_plus_002
    · exact parent_row_oscillation_plus_003
    · exact parent_row_oscillation_plus_004
    · exact parent_row_oscillation_plus_005
    · exact parent_row_oscillation_plus_006
    · exact parent_row_oscillation_plus_007
    · exact parent_row_oscillation_plus_008
    · exact parent_row_oscillation_plus_009
    · exact parent_row_oscillation_plus_010
    · exact parent_row_oscillation_plus_011
    · exact parent_row_oscillation_plus_012
    · exact parent_row_oscillation_plus_013
    · exact parent_row_oscillation_plus_014
    · exact parent_row_oscillation_plus_015
    · exact parent_row_oscillation_plus_016

end
end ASDExplicitGamma.Native
