module

public import ASDExplicitGamma.Native.ParentRowMeanSlopeExpr
public import ASDExplicitGamma.Native.ParentRowCertificates

/-! Exact source and derivative multiplier fields for all sixteen parent rows. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native Numerics.Mirror
noncomputable section

/-- Literal source expressions for the two multiplier coefficients. -/
def parentRowMultiplierExpr (height : ℕ) (derivative : Bool) : Expr :=
  let x := Expr.sqrt (.mul (parentRowWeightedExpr parentRowA2Weight height) (.const (156/5)))
  let y := Expr.sqrt (.mul (parentRowWeightedExpr parentRowA4Weight height) (.const (46488/25)))
  if derivative then .add (.mul x (.const (637/1000))) (.mul y (.const (418/3125)))
  else .add (.mul (.mul (.sqrt (.const (3991821961/14762250000))) (.const 243)) x)
    (.mul y (.const (22599/250)))

/-- Readable multiplier values before outward panel integration. -/
def parentRowMultiplierValue (height : ℕ) (derivative : Bool) : ℝ :=
  let x := Real.sqrt (parentRowWeightedClock parentRowA2Weight height*(156/5))
  let y := Real.sqrt (parentRowWeightedClock parentRowA4Weight height*(46488/25))
  if derivative then x*(637/1000)+y*(418/3125)
  else (Real.sqrt (3991821961/14762250000:ℝ)*243)*x+y*(22599/250)

/-- Exact real meaning of the multiplier source expressions. -/
theorem parent_row_multiplier_expr_eval (env : ℕ → ℝ)
    (hlog : env 2=Real.log 3) (height : ℕ) (derivative : Bool) :
    evalReal env (parentRowMultiplierExpr height derivative)=parentRowMultiplierValue height derivative := by
  cases derivative <;> simp only [parentRowMultiplierExpr,parentRowMultiplierValue,
    Bool.false_eq_true,ite_false,ite_true,evalReal,
    parent_row_weighted_expr_eval env hlog,Rat.cast_div,Rat.cast_ofNat]

/-- Exact source multiplier at height 1. -/
theorem parent_row_multiplier_source_001 :
    nativeSetupParent001FieldsR.getD 2 0=parentRowMultiplierValue 1 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent001A0 nativeSetupParent001Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent001A0 nativeSetupParent001Xi0 := by rfl
  have hl : (nativeSetupParent001Ops.drop 110).length=335 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent001Ops.take 110)).getD 0 (.const 0)=parentRowMultiplierExpr 1 false := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent001Ops.take 110) (nativeSetupParent001Ops.drop 110) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_multiplier_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent001FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent001Real] using hh

/-- Exact derivative multiplier at height 1. -/
theorem parent_row_multiplier_derivative_001 :
    nativeSetupParent001FieldsR.getD 3 0=parentRowMultiplierValue 1 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent001A0 nativeSetupParent001Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent001A0 nativeSetupParent001Xi0 := by rfl
  have hl : (nativeSetupParent001Ops.drop 60).length=385 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent001Ops.take 60)).getD 0 (.const 0)=parentRowMultiplierExpr 1 true := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent001Ops.take 60) (nativeSetupParent001Ops.drop 60) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_multiplier_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent001FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent001Real] using hh

/-- Exact source multiplier at height 2. -/
theorem parent_row_multiplier_source_002 :
    nativeSetupParent002FieldsR.getD 2 0=parentRowMultiplierValue 2 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent002A0 nativeSetupParent002Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent002A0 nativeSetupParent002Xi0 := by rfl
  have hl : (nativeSetupParent002Ops.drop 141).length=332 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent002Ops.take 141)).getD 0 (.const 0)=parentRowMultiplierExpr 2 false := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent002Ops.take 141) (nativeSetupParent002Ops.drop 141) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_multiplier_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent002FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent002Real] using hh

/-- Exact derivative multiplier at height 2. -/
theorem parent_row_multiplier_derivative_002 :
    nativeSetupParent002FieldsR.getD 3 0=parentRowMultiplierValue 2 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent002A0 nativeSetupParent002Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent002A0 nativeSetupParent002Xi0 := by rfl
  have hl : (nativeSetupParent002Ops.drop 71).length=402 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent002Ops.take 71)).getD 0 (.const 0)=parentRowMultiplierExpr 2 true := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent002Ops.take 71) (nativeSetupParent002Ops.drop 71) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_multiplier_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent002FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent002Real] using hh

/-- Exact source multiplier at height 3. -/
theorem parent_row_multiplier_source_003 :
    nativeSetupParent003FieldsR.getD 2 0=parentRowMultiplierValue 3 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent003A0 nativeSetupParent003Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent003A0 nativeSetupParent003Xi0 := by rfl
  have hl : (nativeSetupParent003Ops.drop 172).length=329 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent003Ops.take 172)).getD 0 (.const 0)=parentRowMultiplierExpr 3 false := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent003Ops.take 172) (nativeSetupParent003Ops.drop 172) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_multiplier_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent003FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent003Real] using hh

/-- Exact derivative multiplier at height 3. -/
theorem parent_row_multiplier_derivative_003 :
    nativeSetupParent003FieldsR.getD 3 0=parentRowMultiplierValue 3 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent003A0 nativeSetupParent003Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent003A0 nativeSetupParent003Xi0 := by rfl
  have hl : (nativeSetupParent003Ops.drop 82).length=419 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent003Ops.take 82)).getD 0 (.const 0)=parentRowMultiplierExpr 3 true := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent003Ops.take 82) (nativeSetupParent003Ops.drop 82) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_multiplier_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent003FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent003Real] using hh

/-- Exact source multiplier at height 4. -/
theorem parent_row_multiplier_source_004 :
    nativeSetupParent004FieldsR.getD 2 0=parentRowMultiplierValue 4 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent004A0 nativeSetupParent004Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent004A0 nativeSetupParent004Xi0 := by rfl
  have hl : (nativeSetupParent004Ops.drop 203).length=326 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent004Ops.take 203)).getD 0 (.const 0)=parentRowMultiplierExpr 4 false := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent004Ops.take 203) (nativeSetupParent004Ops.drop 203) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_multiplier_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent004FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent004Real] using hh

/-- Exact derivative multiplier at height 4. -/
theorem parent_row_multiplier_derivative_004 :
    nativeSetupParent004FieldsR.getD 3 0=parentRowMultiplierValue 4 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent004A0 nativeSetupParent004Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent004A0 nativeSetupParent004Xi0 := by rfl
  have hl : (nativeSetupParent004Ops.drop 93).length=436 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent004Ops.take 93)).getD 0 (.const 0)=parentRowMultiplierExpr 4 true := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent004Ops.take 93) (nativeSetupParent004Ops.drop 93) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_multiplier_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent004FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent004Real] using hh

/-- Exact source multiplier at height 5. -/
theorem parent_row_multiplier_source_005 :
    nativeSetupParent005FieldsR.getD 2 0=parentRowMultiplierValue 5 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent005A0 nativeSetupParent005Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent005A0 nativeSetupParent005Xi0 := by rfl
  have hl : (nativeSetupParent005Ops.drop 234).length=323 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent005Ops.take 234)).getD 0 (.const 0)=parentRowMultiplierExpr 5 false := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent005Ops.take 234) (nativeSetupParent005Ops.drop 234) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_multiplier_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent005FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent005Real] using hh

/-- Exact derivative multiplier at height 5. -/
theorem parent_row_multiplier_derivative_005 :
    nativeSetupParent005FieldsR.getD 3 0=parentRowMultiplierValue 5 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent005A0 nativeSetupParent005Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent005A0 nativeSetupParent005Xi0 := by rfl
  have hl : (nativeSetupParent005Ops.drop 104).length=453 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent005Ops.take 104)).getD 0 (.const 0)=parentRowMultiplierExpr 5 true := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent005Ops.take 104) (nativeSetupParent005Ops.drop 104) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_multiplier_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent005FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent005Real] using hh

/-- Exact source multiplier at height 6. -/
theorem parent_row_multiplier_source_006 :
    nativeSetupParent006FieldsR.getD 2 0=parentRowMultiplierValue 6 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent006A0 nativeSetupParent006Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent006A0 nativeSetupParent006Xi0 := by rfl
  have hl : (nativeSetupParent006Ops.drop 265).length=323 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent006Ops.take 265)).getD 0 (.const 0)=parentRowMultiplierExpr 6 false := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent006Ops.take 265) (nativeSetupParent006Ops.drop 265) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_multiplier_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent006FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent006Real] using hh

/-- Exact derivative multiplier at height 6. -/
theorem parent_row_multiplier_derivative_006 :
    nativeSetupParent006FieldsR.getD 3 0=parentRowMultiplierValue 6 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent006A0 nativeSetupParent006Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent006A0 nativeSetupParent006Xi0 := by rfl
  have hl : (nativeSetupParent006Ops.drop 115).length=473 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent006Ops.take 115)).getD 0 (.const 0)=parentRowMultiplierExpr 6 true := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent006Ops.take 115) (nativeSetupParent006Ops.drop 115) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_multiplier_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent006FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent006Real] using hh

/-- Exact source multiplier at height 7. -/
theorem parent_row_multiplier_source_007 :
    nativeSetupParent007FieldsR.getD 2 0=parentRowMultiplierValue 7 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent007A0 nativeSetupParent007Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent007A0 nativeSetupParent007Xi0 := by rfl
  have hl : (nativeSetupParent007Ops.drop 295).length=323 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent007Ops.take 295)).getD 0 (.const 0)=parentRowMultiplierExpr 7 false := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent007Ops.take 295) (nativeSetupParent007Ops.drop 295) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_multiplier_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent007FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent007Real] using hh

/-- Exact derivative multiplier at height 7. -/
theorem parent_row_multiplier_derivative_007 :
    nativeSetupParent007FieldsR.getD 3 0=parentRowMultiplierValue 7 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent007A0 nativeSetupParent007Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent007A0 nativeSetupParent007Xi0 := by rfl
  have hl : (nativeSetupParent007Ops.drop 125).length=493 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent007Ops.take 125)).getD 0 (.const 0)=parentRowMultiplierExpr 7 true := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent007Ops.take 125) (nativeSetupParent007Ops.drop 125) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_multiplier_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent007FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent007Real] using hh

/-- Exact source multiplier at height 8. -/
theorem parent_row_multiplier_source_008 :
    nativeSetupParent008FieldsR.getD 2 0=parentRowMultiplierValue 8 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent008A0 nativeSetupParent008Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent008A0 nativeSetupParent008Xi0 := by rfl
  have hl : (nativeSetupParent008Ops.drop 326).length=323 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent008Ops.take 326)).getD 0 (.const 0)=parentRowMultiplierExpr 8 false := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent008Ops.take 326) (nativeSetupParent008Ops.drop 326) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_multiplier_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent008FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent008Real] using hh

/-- Exact derivative multiplier at height 8. -/
theorem parent_row_multiplier_derivative_008 :
    nativeSetupParent008FieldsR.getD 3 0=parentRowMultiplierValue 8 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent008A0 nativeSetupParent008Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent008A0 nativeSetupParent008Xi0 := by rfl
  have hl : (nativeSetupParent008Ops.drop 136).length=513 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent008Ops.take 136)).getD 0 (.const 0)=parentRowMultiplierExpr 8 true := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent008Ops.take 136) (nativeSetupParent008Ops.drop 136) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_multiplier_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent008FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent008Real] using hh

/-- Exact source multiplier at height 9. -/
theorem parent_row_multiplier_source_009 :
    nativeSetupParent009FieldsR.getD 2 0=parentRowMultiplierValue 9 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent009A0 nativeSetupParent009Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent009A0 nativeSetupParent009Xi0 := by rfl
  have hl : (nativeSetupParent009Ops.drop 356).length=323 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent009Ops.take 356)).getD 0 (.const 0)=parentRowMultiplierExpr 9 false := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent009Ops.take 356) (nativeSetupParent009Ops.drop 356) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_multiplier_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent009FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent009Real] using hh

/-- Exact derivative multiplier at height 9. -/
theorem parent_row_multiplier_derivative_009 :
    nativeSetupParent009FieldsR.getD 3 0=parentRowMultiplierValue 9 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent009A0 nativeSetupParent009Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent009A0 nativeSetupParent009Xi0 := by rfl
  have hl : (nativeSetupParent009Ops.drop 146).length=533 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent009Ops.take 146)).getD 0 (.const 0)=parentRowMultiplierExpr 9 true := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent009Ops.take 146) (nativeSetupParent009Ops.drop 146) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_multiplier_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent009FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent009Real] using hh

/-- Exact source multiplier at height 10. -/
theorem parent_row_multiplier_source_010 :
    nativeSetupParent010FieldsR.getD 2 0=parentRowMultiplierValue 10 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent010A0 nativeSetupParent010Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent010A0 nativeSetupParent010Xi0 := by rfl
  have hl : (nativeSetupParent010Ops.drop 387).length=323 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent010Ops.take 387)).getD 0 (.const 0)=parentRowMultiplierExpr 10 false := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent010Ops.take 387) (nativeSetupParent010Ops.drop 387) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_multiplier_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent010FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent010Real] using hh

/-- Exact derivative multiplier at height 10. -/
theorem parent_row_multiplier_derivative_010 :
    nativeSetupParent010FieldsR.getD 3 0=parentRowMultiplierValue 10 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent010A0 nativeSetupParent010Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent010A0 nativeSetupParent010Xi0 := by rfl
  have hl : (nativeSetupParent010Ops.drop 157).length=553 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent010Ops.take 157)).getD 0 (.const 0)=parentRowMultiplierExpr 10 true := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent010Ops.take 157) (nativeSetupParent010Ops.drop 157) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_multiplier_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent010FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent010Real] using hh

/-- Exact source multiplier at height 11. -/
theorem parent_row_multiplier_source_011 :
    nativeSetupParent011FieldsR.getD 2 0=parentRowMultiplierValue 11 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent011A0 nativeSetupParent011Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent011A0 nativeSetupParent011Xi0 := by rfl
  have hl : (nativeSetupParent011Ops.drop 417).length=323 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent011Ops.take 417)).getD 0 (.const 0)=parentRowMultiplierExpr 11 false := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent011Ops.take 417) (nativeSetupParent011Ops.drop 417) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_multiplier_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent011FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent011Real] using hh

/-- Exact derivative multiplier at height 11. -/
theorem parent_row_multiplier_derivative_011 :
    nativeSetupParent011FieldsR.getD 3 0=parentRowMultiplierValue 11 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent011A0 nativeSetupParent011Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent011A0 nativeSetupParent011Xi0 := by rfl
  have hl : (nativeSetupParent011Ops.drop 167).length=573 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent011Ops.take 167)).getD 0 (.const 0)=parentRowMultiplierExpr 11 true := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent011Ops.take 167) (nativeSetupParent011Ops.drop 167) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_multiplier_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent011FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent011Real] using hh

/-- Exact source multiplier at height 12. -/
theorem parent_row_multiplier_source_012 :
    nativeSetupParent012FieldsR.getD 2 0=parentRowMultiplierValue 12 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent012A0 nativeSetupParent012Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent012A0 nativeSetupParent012Xi0 := by rfl
  have hl : (nativeSetupParent012Ops.drop 448).length=323 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent012Ops.take 448)).getD 0 (.const 0)=parentRowMultiplierExpr 12 false := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent012Ops.take 448) (nativeSetupParent012Ops.drop 448) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_multiplier_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent012FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent012Real] using hh

/-- Exact derivative multiplier at height 12. -/
theorem parent_row_multiplier_derivative_012 :
    nativeSetupParent012FieldsR.getD 3 0=parentRowMultiplierValue 12 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent012A0 nativeSetupParent012Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent012A0 nativeSetupParent012Xi0 := by rfl
  have hl : (nativeSetupParent012Ops.drop 178).length=593 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent012Ops.take 178)).getD 0 (.const 0)=parentRowMultiplierExpr 12 true := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent012Ops.take 178) (nativeSetupParent012Ops.drop 178) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_multiplier_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent012FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent012Real] using hh

/-- Exact source multiplier at height 13. -/
theorem parent_row_multiplier_source_013 :
    nativeSetupParent013FieldsR.getD 2 0=parentRowMultiplierValue 13 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent013A0 nativeSetupParent013Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent013A0 nativeSetupParent013Xi0 := by rfl
  have hl : (nativeSetupParent013Ops.drop 478).length=323 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent013Ops.take 478)).getD 0 (.const 0)=parentRowMultiplierExpr 13 false := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent013Ops.take 478) (nativeSetupParent013Ops.drop 478) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_multiplier_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent013FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent013Real] using hh

/-- Exact derivative multiplier at height 13. -/
theorem parent_row_multiplier_derivative_013 :
    nativeSetupParent013FieldsR.getD 3 0=parentRowMultiplierValue 13 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent013A0 nativeSetupParent013Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent013A0 nativeSetupParent013Xi0 := by rfl
  have hl : (nativeSetupParent013Ops.drop 188).length=613 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent013Ops.take 188)).getD 0 (.const 0)=parentRowMultiplierExpr 13 true := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent013Ops.take 188) (nativeSetupParent013Ops.drop 188) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_multiplier_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent013FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent013Real] using hh

/-- Exact source multiplier at height 14. -/
theorem parent_row_multiplier_source_014 :
    nativeSetupParent014FieldsR.getD 2 0=parentRowMultiplierValue 14 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent014A0 nativeSetupParent014Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent014A0 nativeSetupParent014Xi0 := by rfl
  have hl : (nativeSetupParent014Ops.drop 509).length=323 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent014Ops.take 509)).getD 0 (.const 0)=parentRowMultiplierExpr 14 false := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent014Ops.take 509) (nativeSetupParent014Ops.drop 509) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_multiplier_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent014FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent014Real] using hh

/-- Exact derivative multiplier at height 14. -/
theorem parent_row_multiplier_derivative_014 :
    nativeSetupParent014FieldsR.getD 3 0=parentRowMultiplierValue 14 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent014A0 nativeSetupParent014Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent014A0 nativeSetupParent014Xi0 := by rfl
  have hl : (nativeSetupParent014Ops.drop 199).length=633 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent014Ops.take 199)).getD 0 (.const 0)=parentRowMultiplierExpr 14 true := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent014Ops.take 199) (nativeSetupParent014Ops.drop 199) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_multiplier_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent014FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent014Real] using hh

/-- Exact source multiplier at height 15. -/
theorem parent_row_multiplier_source_015 :
    nativeSetupParent015FieldsR.getD 2 0=parentRowMultiplierValue 15 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent015A0 nativeSetupParent015Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent015A0 nativeSetupParent015Xi0 := by rfl
  have hl : (nativeSetupParent015Ops.drop 539).length=323 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent015Ops.take 539)).getD 0 (.const 0)=parentRowMultiplierExpr 15 false := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent015Ops.take 539) (nativeSetupParent015Ops.drop 539) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_multiplier_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent015FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent015Real] using hh

/-- Exact derivative multiplier at height 15. -/
theorem parent_row_multiplier_derivative_015 :
    nativeSetupParent015FieldsR.getD 3 0=parentRowMultiplierValue 15 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent015A0 nativeSetupParent015Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent015A0 nativeSetupParent015Xi0 := by rfl
  have hl : (nativeSetupParent015Ops.drop 209).length=653 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent015Ops.take 209)).getD 0 (.const 0)=parentRowMultiplierExpr 15 true := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent015Ops.take 209) (nativeSetupParent015Ops.drop 209) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_multiplier_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent015FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent015Real] using hh

/-- Exact source multiplier at height 16. -/
theorem parent_row_multiplier_source_016 :
    nativeSetupParent016FieldsR.getD 2 0=parentRowMultiplierValue 16 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent016A0 nativeSetupParent016Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent016A0 nativeSetupParent016Xi0 := by rfl
  have hl : (nativeSetupParent016Ops.drop 570).length=323 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent016Ops.take 570)).getD 0 (.const 0)=parentRowMultiplierExpr 16 false := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent016Ops.take 570) (nativeSetupParent016Ops.drop 570) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_multiplier_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent016FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent016Real] using hh

/-- Exact derivative multiplier at height 16. -/
theorem parent_row_multiplier_derivative_016 :
    nativeSetupParent016FieldsR.getD 3 0=parentRowMultiplierValue 16 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent016A0 nativeSetupParent016Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent016A0 nativeSetupParent016Xi0 := by rfl
  have hl : (nativeSetupParent016Ops.drop 220).length=673 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent016Ops.take 220)).getD 0 (.const 0)=parentRowMultiplierExpr 16 true := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent016Ops.take 220) (nativeSetupParent016Ops.drop 220) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_multiplier_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent016FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent016Real] using hh

/-- The selected source and derivative multipliers are their exact root clocks. -/
theorem parent_row_multiplier_field (j : Fin 16) (derivative : Bool) :
    (parentRowFields j).getD (if derivative then 3 else 2) 0=
      parentRowMultiplierValue (j.val+1) derivative := by
  cases derivative
  · fin_cases j <;> simp only [Bool.false_eq_true,ite_false,parentRowFields,
      nativeConfiguredParentEndpoint,nativeParentEndpointCertificates,nativeParent001EndpointCertificate,nativeParent002EndpointCertificate,nativeParent003EndpointCertificate,nativeParent004EndpointCertificate,nativeParent005EndpointCertificate,nativeParent006EndpointCertificate,nativeParent007EndpointCertificate,nativeParent008EndpointCertificate,nativeParent009EndpointCertificate,nativeParent010EndpointCertificate,nativeParent011EndpointCertificate,nativeParent012EndpointCertificate,nativeParent013EndpointCertificate,nativeParent014EndpointCertificate,nativeParent015EndpointCertificate,nativeParent016EndpointCertificate,
      List.getD_cons_zero,List.getD_cons_succ]
    · exact parent_row_multiplier_source_001
    · exact parent_row_multiplier_source_002
    · exact parent_row_multiplier_source_003
    · exact parent_row_multiplier_source_004
    · exact parent_row_multiplier_source_005
    · exact parent_row_multiplier_source_006
    · exact parent_row_multiplier_source_007
    · exact parent_row_multiplier_source_008
    · exact parent_row_multiplier_source_009
    · exact parent_row_multiplier_source_010
    · exact parent_row_multiplier_source_011
    · exact parent_row_multiplier_source_012
    · exact parent_row_multiplier_source_013
    · exact parent_row_multiplier_source_014
    · exact parent_row_multiplier_source_015
    · exact parent_row_multiplier_source_016
  · fin_cases j <;> simp only [ite_true,parentRowFields,
      nativeConfiguredParentEndpoint,nativeParentEndpointCertificates,nativeParent001EndpointCertificate,nativeParent002EndpointCertificate,nativeParent003EndpointCertificate,nativeParent004EndpointCertificate,nativeParent005EndpointCertificate,nativeParent006EndpointCertificate,nativeParent007EndpointCertificate,nativeParent008EndpointCertificate,nativeParent009EndpointCertificate,nativeParent010EndpointCertificate,nativeParent011EndpointCertificate,nativeParent012EndpointCertificate,nativeParent013EndpointCertificate,nativeParent014EndpointCertificate,nativeParent015EndpointCertificate,nativeParent016EndpointCertificate,
      List.getD_cons_zero,List.getD_cons_succ]
    · exact parent_row_multiplier_derivative_001
    · exact parent_row_multiplier_derivative_002
    · exact parent_row_multiplier_derivative_003
    · exact parent_row_multiplier_derivative_004
    · exact parent_row_multiplier_derivative_005
    · exact parent_row_multiplier_derivative_006
    · exact parent_row_multiplier_derivative_007
    · exact parent_row_multiplier_derivative_008
    · exact parent_row_multiplier_derivative_009
    · exact parent_row_multiplier_derivative_010
    · exact parent_row_multiplier_derivative_011
    · exact parent_row_multiplier_derivative_012
    · exact parent_row_multiplier_derivative_013
    · exact parent_row_multiplier_derivative_014
    · exact parent_row_multiplier_derivative_015
    · exact parent_row_multiplier_derivative_016

end
end ASDExplicitGamma.Native
