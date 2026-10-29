module

public import ASDExplicitGamma.Native.ParentRowBoundaryExpr
public import ASDExplicitGamma.Native.ParentRowCertificates

/-! Exact separate centered boundary sums in all sixteen parent source programs. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native Numerics.Mirror
noncomputable section

/-- Exact plus boundary sum at parent height 1. -/
theorem parent_row_boundary_plus_001 :
    nativeSetupParent001FieldsR.getD 6 0=parentRowBoundaryValue 1 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent001A0 nativeSetupParent001Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent001A0 nativeSetupParent001Xi0 := by rfl
  have hl : (nativeSetupParent001Ops.drop 90).length=355 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent001Ops.take 90)).getD 0 (.const 0)=parentRowBoundaryExpr true 1 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent001Ops.take 90) (nativeSetupParent001Ops.drop 90) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_boundary_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent001FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent001Real] using hh

/-- Exact minus boundary sum at parent height 1. -/
theorem parent_row_boundary_minus_001 :
    nativeSetupParent001FieldsR.getD 7 0=parentRowBoundaryValue 1 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent001A0 nativeSetupParent001Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent001A0 nativeSetupParent001Xi0 := by rfl
  have hl : (nativeSetupParent001Ops.drop 100).length=345 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent001Ops.take 100)).getD 0 (.const 0)=parentRowBoundaryExpr false 1 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent001Ops.take 100) (nativeSetupParent001Ops.drop 100) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_boundary_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent001FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent001Real] using hh

/-- Exact plus boundary sum at parent height 2. -/
theorem parent_row_boundary_plus_002 :
    nativeSetupParent002FieldsR.getD 6 0=parentRowBoundaryValue 2 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent002A0 nativeSetupParent002Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent002A0 nativeSetupParent002Xi0 := by rfl
  have hl : (nativeSetupParent002Ops.drop 121).length=352 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent002Ops.take 121)).getD 0 (.const 0)=parentRowBoundaryExpr true 2 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent002Ops.take 121) (nativeSetupParent002Ops.drop 121) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_boundary_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent002FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent002Real] using hh

/-- Exact minus boundary sum at parent height 2. -/
theorem parent_row_boundary_minus_002 :
    nativeSetupParent002FieldsR.getD 7 0=parentRowBoundaryValue 2 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent002A0 nativeSetupParent002Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent002A0 nativeSetupParent002Xi0 := by rfl
  have hl : (nativeSetupParent002Ops.drop 131).length=342 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent002Ops.take 131)).getD 0 (.const 0)=parentRowBoundaryExpr false 2 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent002Ops.take 131) (nativeSetupParent002Ops.drop 131) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_boundary_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent002FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent002Real] using hh

/-- Exact plus boundary sum at parent height 3. -/
theorem parent_row_boundary_plus_003 :
    nativeSetupParent003FieldsR.getD 6 0=parentRowBoundaryValue 3 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent003A0 nativeSetupParent003Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent003A0 nativeSetupParent003Xi0 := by rfl
  have hl : (nativeSetupParent003Ops.drop 152).length=349 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent003Ops.take 152)).getD 0 (.const 0)=parentRowBoundaryExpr true 3 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent003Ops.take 152) (nativeSetupParent003Ops.drop 152) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_boundary_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent003FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent003Real] using hh

/-- Exact minus boundary sum at parent height 3. -/
theorem parent_row_boundary_minus_003 :
    nativeSetupParent003FieldsR.getD 7 0=parentRowBoundaryValue 3 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent003A0 nativeSetupParent003Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent003A0 nativeSetupParent003Xi0 := by rfl
  have hl : (nativeSetupParent003Ops.drop 162).length=339 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent003Ops.take 162)).getD 0 (.const 0)=parentRowBoundaryExpr false 3 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent003Ops.take 162) (nativeSetupParent003Ops.drop 162) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_boundary_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent003FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent003Real] using hh

/-- Exact plus boundary sum at parent height 4. -/
theorem parent_row_boundary_plus_004 :
    nativeSetupParent004FieldsR.getD 6 0=parentRowBoundaryValue 4 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent004A0 nativeSetupParent004Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent004A0 nativeSetupParent004Xi0 := by rfl
  have hl : (nativeSetupParent004Ops.drop 183).length=346 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent004Ops.take 183)).getD 0 (.const 0)=parentRowBoundaryExpr true 4 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent004Ops.take 183) (nativeSetupParent004Ops.drop 183) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_boundary_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent004FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent004Real] using hh

/-- Exact minus boundary sum at parent height 4. -/
theorem parent_row_boundary_minus_004 :
    nativeSetupParent004FieldsR.getD 7 0=parentRowBoundaryValue 4 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent004A0 nativeSetupParent004Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent004A0 nativeSetupParent004Xi0 := by rfl
  have hl : (nativeSetupParent004Ops.drop 193).length=336 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent004Ops.take 193)).getD 0 (.const 0)=parentRowBoundaryExpr false 4 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent004Ops.take 193) (nativeSetupParent004Ops.drop 193) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_boundary_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent004FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent004Real] using hh

/-- Exact plus boundary sum at parent height 5. -/
theorem parent_row_boundary_plus_005 :
    nativeSetupParent005FieldsR.getD 6 0=parentRowBoundaryValue 5 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent005A0 nativeSetupParent005Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent005A0 nativeSetupParent005Xi0 := by rfl
  have hl : (nativeSetupParent005Ops.drop 214).length=343 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent005Ops.take 214)).getD 0 (.const 0)=parentRowBoundaryExpr true 5 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent005Ops.take 214) (nativeSetupParent005Ops.drop 214) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_boundary_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent005FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent005Real] using hh

/-- Exact minus boundary sum at parent height 5. -/
theorem parent_row_boundary_minus_005 :
    nativeSetupParent005FieldsR.getD 7 0=parentRowBoundaryValue 5 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent005A0 nativeSetupParent005Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent005A0 nativeSetupParent005Xi0 := by rfl
  have hl : (nativeSetupParent005Ops.drop 224).length=333 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent005Ops.take 224)).getD 0 (.const 0)=parentRowBoundaryExpr false 5 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent005Ops.take 224) (nativeSetupParent005Ops.drop 224) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_boundary_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent005FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent005Real] using hh

/-- Exact plus boundary sum at parent height 6. -/
theorem parent_row_boundary_plus_006 :
    nativeSetupParent006FieldsR.getD 6 0=parentRowBoundaryValue 6 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent006A0 nativeSetupParent006Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent006A0 nativeSetupParent006Xi0 := by rfl
  have hl : (nativeSetupParent006Ops.drop 245).length=343 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent006Ops.take 245)).getD 0 (.const 0)=parentRowBoundaryExpr true 6 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent006Ops.take 245) (nativeSetupParent006Ops.drop 245) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_boundary_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent006FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent006Real] using hh

/-- Exact minus boundary sum at parent height 6. -/
theorem parent_row_boundary_minus_006 :
    nativeSetupParent006FieldsR.getD 7 0=parentRowBoundaryValue 6 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent006A0 nativeSetupParent006Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent006A0 nativeSetupParent006Xi0 := by rfl
  have hl : (nativeSetupParent006Ops.drop 255).length=333 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent006Ops.take 255)).getD 0 (.const 0)=parentRowBoundaryExpr false 6 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent006Ops.take 255) (nativeSetupParent006Ops.drop 255) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_boundary_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent006FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent006Real] using hh

/-- Exact plus boundary sum at parent height 7. -/
theorem parent_row_boundary_plus_007 :
    nativeSetupParent007FieldsR.getD 6 0=parentRowBoundaryValue 7 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent007A0 nativeSetupParent007Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent007A0 nativeSetupParent007Xi0 := by rfl
  have hl : (nativeSetupParent007Ops.drop 275).length=343 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent007Ops.take 275)).getD 0 (.const 0)=parentRowBoundaryExpr true 7 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent007Ops.take 275) (nativeSetupParent007Ops.drop 275) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_boundary_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent007FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent007Real] using hh

/-- Exact minus boundary sum at parent height 7. -/
theorem parent_row_boundary_minus_007 :
    nativeSetupParent007FieldsR.getD 7 0=parentRowBoundaryValue 7 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent007A0 nativeSetupParent007Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent007A0 nativeSetupParent007Xi0 := by rfl
  have hl : (nativeSetupParent007Ops.drop 285).length=333 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent007Ops.take 285)).getD 0 (.const 0)=parentRowBoundaryExpr false 7 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent007Ops.take 285) (nativeSetupParent007Ops.drop 285) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_boundary_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent007FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent007Real] using hh

/-- Exact plus boundary sum at parent height 8. -/
theorem parent_row_boundary_plus_008 :
    nativeSetupParent008FieldsR.getD 6 0=parentRowBoundaryValue 8 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent008A0 nativeSetupParent008Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent008A0 nativeSetupParent008Xi0 := by rfl
  have hl : (nativeSetupParent008Ops.drop 306).length=343 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent008Ops.take 306)).getD 0 (.const 0)=parentRowBoundaryExpr true 8 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent008Ops.take 306) (nativeSetupParent008Ops.drop 306) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_boundary_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent008FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent008Real] using hh

/-- Exact minus boundary sum at parent height 8. -/
theorem parent_row_boundary_minus_008 :
    nativeSetupParent008FieldsR.getD 7 0=parentRowBoundaryValue 8 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent008A0 nativeSetupParent008Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent008A0 nativeSetupParent008Xi0 := by rfl
  have hl : (nativeSetupParent008Ops.drop 316).length=333 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent008Ops.take 316)).getD 0 (.const 0)=parentRowBoundaryExpr false 8 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent008Ops.take 316) (nativeSetupParent008Ops.drop 316) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_boundary_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent008FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent008Real] using hh

/-- Exact plus boundary sum at parent height 9. -/
theorem parent_row_boundary_plus_009 :
    nativeSetupParent009FieldsR.getD 6 0=parentRowBoundaryValue 9 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent009A0 nativeSetupParent009Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent009A0 nativeSetupParent009Xi0 := by rfl
  have hl : (nativeSetupParent009Ops.drop 336).length=343 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent009Ops.take 336)).getD 0 (.const 0)=parentRowBoundaryExpr true 9 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent009Ops.take 336) (nativeSetupParent009Ops.drop 336) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_boundary_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent009FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent009Real] using hh

/-- Exact minus boundary sum at parent height 9. -/
theorem parent_row_boundary_minus_009 :
    nativeSetupParent009FieldsR.getD 7 0=parentRowBoundaryValue 9 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent009A0 nativeSetupParent009Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent009A0 nativeSetupParent009Xi0 := by rfl
  have hl : (nativeSetupParent009Ops.drop 346).length=333 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent009Ops.take 346)).getD 0 (.const 0)=parentRowBoundaryExpr false 9 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent009Ops.take 346) (nativeSetupParent009Ops.drop 346) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_boundary_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent009FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent009Real] using hh

/-- Exact plus boundary sum at parent height 10. -/
theorem parent_row_boundary_plus_010 :
    nativeSetupParent010FieldsR.getD 6 0=parentRowBoundaryValue 10 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent010A0 nativeSetupParent010Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent010A0 nativeSetupParent010Xi0 := by rfl
  have hl : (nativeSetupParent010Ops.drop 367).length=343 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent010Ops.take 367)).getD 0 (.const 0)=parentRowBoundaryExpr true 10 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent010Ops.take 367) (nativeSetupParent010Ops.drop 367) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_boundary_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent010FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent010Real] using hh

/-- Exact minus boundary sum at parent height 10. -/
theorem parent_row_boundary_minus_010 :
    nativeSetupParent010FieldsR.getD 7 0=parentRowBoundaryValue 10 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent010A0 nativeSetupParent010Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent010A0 nativeSetupParent010Xi0 := by rfl
  have hl : (nativeSetupParent010Ops.drop 377).length=333 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent010Ops.take 377)).getD 0 (.const 0)=parentRowBoundaryExpr false 10 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent010Ops.take 377) (nativeSetupParent010Ops.drop 377) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_boundary_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent010FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent010Real] using hh

/-- Exact plus boundary sum at parent height 11. -/
theorem parent_row_boundary_plus_011 :
    nativeSetupParent011FieldsR.getD 6 0=parentRowBoundaryValue 11 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent011A0 nativeSetupParent011Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent011A0 nativeSetupParent011Xi0 := by rfl
  have hl : (nativeSetupParent011Ops.drop 397).length=343 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent011Ops.take 397)).getD 0 (.const 0)=parentRowBoundaryExpr true 11 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent011Ops.take 397) (nativeSetupParent011Ops.drop 397) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_boundary_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent011FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent011Real] using hh

/-- Exact minus boundary sum at parent height 11. -/
theorem parent_row_boundary_minus_011 :
    nativeSetupParent011FieldsR.getD 7 0=parentRowBoundaryValue 11 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent011A0 nativeSetupParent011Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent011A0 nativeSetupParent011Xi0 := by rfl
  have hl : (nativeSetupParent011Ops.drop 407).length=333 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent011Ops.take 407)).getD 0 (.const 0)=parentRowBoundaryExpr false 11 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent011Ops.take 407) (nativeSetupParent011Ops.drop 407) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_boundary_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent011FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent011Real] using hh

/-- Exact plus boundary sum at parent height 12. -/
theorem parent_row_boundary_plus_012 :
    nativeSetupParent012FieldsR.getD 6 0=parentRowBoundaryValue 12 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent012A0 nativeSetupParent012Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent012A0 nativeSetupParent012Xi0 := by rfl
  have hl : (nativeSetupParent012Ops.drop 428).length=343 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent012Ops.take 428)).getD 0 (.const 0)=parentRowBoundaryExpr true 12 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent012Ops.take 428) (nativeSetupParent012Ops.drop 428) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_boundary_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent012FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent012Real] using hh

/-- Exact minus boundary sum at parent height 12. -/
theorem parent_row_boundary_minus_012 :
    nativeSetupParent012FieldsR.getD 7 0=parentRowBoundaryValue 12 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent012A0 nativeSetupParent012Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent012A0 nativeSetupParent012Xi0 := by rfl
  have hl : (nativeSetupParent012Ops.drop 438).length=333 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent012Ops.take 438)).getD 0 (.const 0)=parentRowBoundaryExpr false 12 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent012Ops.take 438) (nativeSetupParent012Ops.drop 438) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_boundary_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent012FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent012Real] using hh

/-- Exact plus boundary sum at parent height 13. -/
theorem parent_row_boundary_plus_013 :
    nativeSetupParent013FieldsR.getD 6 0=parentRowBoundaryValue 13 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent013A0 nativeSetupParent013Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent013A0 nativeSetupParent013Xi0 := by rfl
  have hl : (nativeSetupParent013Ops.drop 458).length=343 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent013Ops.take 458)).getD 0 (.const 0)=parentRowBoundaryExpr true 13 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent013Ops.take 458) (nativeSetupParent013Ops.drop 458) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_boundary_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent013FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent013Real] using hh

/-- Exact minus boundary sum at parent height 13. -/
theorem parent_row_boundary_minus_013 :
    nativeSetupParent013FieldsR.getD 7 0=parentRowBoundaryValue 13 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent013A0 nativeSetupParent013Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent013A0 nativeSetupParent013Xi0 := by rfl
  have hl : (nativeSetupParent013Ops.drop 468).length=333 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent013Ops.take 468)).getD 0 (.const 0)=parentRowBoundaryExpr false 13 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent013Ops.take 468) (nativeSetupParent013Ops.drop 468) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_boundary_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent013FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent013Real] using hh

/-- Exact plus boundary sum at parent height 14. -/
theorem parent_row_boundary_plus_014 :
    nativeSetupParent014FieldsR.getD 6 0=parentRowBoundaryValue 14 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent014A0 nativeSetupParent014Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent014A0 nativeSetupParent014Xi0 := by rfl
  have hl : (nativeSetupParent014Ops.drop 489).length=343 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent014Ops.take 489)).getD 0 (.const 0)=parentRowBoundaryExpr true 14 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent014Ops.take 489) (nativeSetupParent014Ops.drop 489) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_boundary_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent014FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent014Real] using hh

/-- Exact minus boundary sum at parent height 14. -/
theorem parent_row_boundary_minus_014 :
    nativeSetupParent014FieldsR.getD 7 0=parentRowBoundaryValue 14 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent014A0 nativeSetupParent014Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent014A0 nativeSetupParent014Xi0 := by rfl
  have hl : (nativeSetupParent014Ops.drop 499).length=333 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent014Ops.take 499)).getD 0 (.const 0)=parentRowBoundaryExpr false 14 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent014Ops.take 499) (nativeSetupParent014Ops.drop 499) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_boundary_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent014FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent014Real] using hh

/-- Exact plus boundary sum at parent height 15. -/
theorem parent_row_boundary_plus_015 :
    nativeSetupParent015FieldsR.getD 6 0=parentRowBoundaryValue 15 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent015A0 nativeSetupParent015Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent015A0 nativeSetupParent015Xi0 := by rfl
  have hl : (nativeSetupParent015Ops.drop 519).length=343 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent015Ops.take 519)).getD 0 (.const 0)=parentRowBoundaryExpr true 15 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent015Ops.take 519) (nativeSetupParent015Ops.drop 519) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_boundary_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent015FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent015Real] using hh

/-- Exact minus boundary sum at parent height 15. -/
theorem parent_row_boundary_minus_015 :
    nativeSetupParent015FieldsR.getD 7 0=parentRowBoundaryValue 15 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent015A0 nativeSetupParent015Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent015A0 nativeSetupParent015Xi0 := by rfl
  have hl : (nativeSetupParent015Ops.drop 529).length=333 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent015Ops.take 529)).getD 0 (.const 0)=parentRowBoundaryExpr false 15 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent015Ops.take 529) (nativeSetupParent015Ops.drop 529) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_boundary_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent015FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent015Real] using hh

/-- Exact plus boundary sum at parent height 16. -/
theorem parent_row_boundary_plus_016 :
    nativeSetupParent016FieldsR.getD 6 0=parentRowBoundaryValue 16 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent016A0 nativeSetupParent016Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent016A0 nativeSetupParent016Xi0 := by rfl
  have hl : (nativeSetupParent016Ops.drop 550).length=343 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent016Ops.take 550)).getD 0 (.const 0)=parentRowBoundaryExpr true 16 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent016Ops.take 550) (nativeSetupParent016Ops.drop 550) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_boundary_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent016FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent016Real] using hh

/-- Exact minus boundary sum at parent height 16. -/
theorem parent_row_boundary_minus_016 :
    nativeSetupParent016FieldsR.getD 7 0=parentRowBoundaryValue 16 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent016A0 nativeSetupParent016Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent016A0 nativeSetupParent016Xi0 := by rfl
  have hl : (nativeSetupParent016Ops.drop 560).length=333 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent016Ops.take 560)).getD 0 (.const 0)=parentRowBoundaryExpr false 16 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent016Ops.take 560) (nativeSetupParent016Ops.drop 560) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_boundary_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent016FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent016Real] using hh

/-- Each selected boundary field retains its own exact weighted sum. -/
theorem parent_row_boundary_field (j : Fin 16) (plus : Bool) :
    (parentRowFields j).getD (if plus then 6 else 7) 0=
      parentRowBoundaryValue (j.val+1) plus := by
  cases plus
  · fin_cases j <;> simp only [Bool.false_eq_true,ite_false,parentRowFields,
      nativeConfiguredParentEndpoint,nativeParentEndpointCertificates,nativeParent001EndpointCertificate,nativeParent002EndpointCertificate,nativeParent003EndpointCertificate,nativeParent004EndpointCertificate,nativeParent005EndpointCertificate,nativeParent006EndpointCertificate,nativeParent007EndpointCertificate,nativeParent008EndpointCertificate,nativeParent009EndpointCertificate,nativeParent010EndpointCertificate,nativeParent011EndpointCertificate,nativeParent012EndpointCertificate,nativeParent013EndpointCertificate,nativeParent014EndpointCertificate,nativeParent015EndpointCertificate,nativeParent016EndpointCertificate,
      List.getD_cons_zero,List.getD_cons_succ]
    · exact parent_row_boundary_minus_001
    · exact parent_row_boundary_minus_002
    · exact parent_row_boundary_minus_003
    · exact parent_row_boundary_minus_004
    · exact parent_row_boundary_minus_005
    · exact parent_row_boundary_minus_006
    · exact parent_row_boundary_minus_007
    · exact parent_row_boundary_minus_008
    · exact parent_row_boundary_minus_009
    · exact parent_row_boundary_minus_010
    · exact parent_row_boundary_minus_011
    · exact parent_row_boundary_minus_012
    · exact parent_row_boundary_minus_013
    · exact parent_row_boundary_minus_014
    · exact parent_row_boundary_minus_015
    · exact parent_row_boundary_minus_016
  · fin_cases j <;> simp only [ite_true,parentRowFields,
      nativeConfiguredParentEndpoint,nativeParentEndpointCertificates,nativeParent001EndpointCertificate,nativeParent002EndpointCertificate,nativeParent003EndpointCertificate,nativeParent004EndpointCertificate,nativeParent005EndpointCertificate,nativeParent006EndpointCertificate,nativeParent007EndpointCertificate,nativeParent008EndpointCertificate,nativeParent009EndpointCertificate,nativeParent010EndpointCertificate,nativeParent011EndpointCertificate,nativeParent012EndpointCertificate,nativeParent013EndpointCertificate,nativeParent014EndpointCertificate,nativeParent015EndpointCertificate,nativeParent016EndpointCertificate,
      List.getD_cons_zero,List.getD_cons_succ]
    · exact parent_row_boundary_plus_001
    · exact parent_row_boundary_plus_002
    · exact parent_row_boundary_plus_003
    · exact parent_row_boundary_plus_004
    · exact parent_row_boundary_plus_005
    · exact parent_row_boundary_plus_006
    · exact parent_row_boundary_plus_007
    · exact parent_row_boundary_plus_008
    · exact parent_row_boundary_plus_009
    · exact parent_row_boundary_plus_010
    · exact parent_row_boundary_plus_011
    · exact parent_row_boundary_plus_012
    · exact parent_row_boundary_plus_013
    · exact parent_row_boundary_plus_014
    · exact parent_row_boundary_plus_015
    · exact parent_row_boundary_plus_016

end
end ASDExplicitGamma.Native
