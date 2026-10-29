module

public import ASDExplicitGamma.Native.ParentRowWeightedClocks
public import ASDExplicitGamma.Native.ParentRowCertificates

/-! Exact weighted parent coefficients in all sixteen certified source setups. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native Numerics.Mirror
noncomputable section

/-- The exact depth-1 Y coefficient is its physical shell sum. -/
theorem parent_row_y_001 :
    nativeSetupParent001FieldsR.getD 16 0=parentRowWeightedClock parentRowYWeight 1 := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent001A0 nativeSetupParent001Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent001A0 nativeSetupParent001Xi0 := by rfl
  have hl : (nativeSetupParent001Ops.drop 80).length=365 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent001Ops.take 80)).getD 0 (.const 0)=parentRowWeightedExpr parentRowYWeight 1 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent001Ops.take 80) (nativeSetupParent001Ops.drop 80) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent001FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent001Real]
  rw [hh,parent_row_weighted_expr_eval env (by rfl)]

/-- The exact depth-2 Y coefficient is its physical shell sum. -/
theorem parent_row_y_002 :
    nativeSetupParent002FieldsR.getD 16 0=parentRowWeightedClock parentRowYWeight 2 := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent002A0 nativeSetupParent002Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent002A0 nativeSetupParent002Xi0 := by rfl
  have hl : (nativeSetupParent002Ops.drop 114).length=359 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent002Ops.take 114)).getD 0 (.const 0)=parentRowWeightedExpr parentRowYWeight 2 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent002Ops.take 114) (nativeSetupParent002Ops.drop 114) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent002FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent002Real]
  rw [hh,parent_row_weighted_expr_eval env (by rfl)]

/-- The exact depth-3 Y coefficient is its physical shell sum. -/
theorem parent_row_y_003 :
    nativeSetupParent003FieldsR.getD 16 0=parentRowWeightedClock parentRowYWeight 3 := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent003A0 nativeSetupParent003Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent003A0 nativeSetupParent003Xi0 := by rfl
  have hl : (nativeSetupParent003Ops.drop 145).length=356 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent003Ops.take 145)).getD 0 (.const 0)=parentRowWeightedExpr parentRowYWeight 3 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent003Ops.take 145) (nativeSetupParent003Ops.drop 145) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent003FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent003Real]
  rw [hh,parent_row_weighted_expr_eval env (by rfl)]

/-- The exact depth-4 Y coefficient is its physical shell sum. -/
theorem parent_row_y_004 :
    nativeSetupParent004FieldsR.getD 16 0=parentRowWeightedClock parentRowYWeight 4 := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent004A0 nativeSetupParent004Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent004A0 nativeSetupParent004Xi0 := by rfl
  have hl : (nativeSetupParent004Ops.drop 176).length=353 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent004Ops.take 176)).getD 0 (.const 0)=parentRowWeightedExpr parentRowYWeight 4 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent004Ops.take 176) (nativeSetupParent004Ops.drop 176) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent004FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent004Real]
  rw [hh,parent_row_weighted_expr_eval env (by rfl)]

/-- The exact depth-5 Y coefficient is its physical shell sum. -/
theorem parent_row_y_005 :
    nativeSetupParent005FieldsR.getD 16 0=parentRowWeightedClock parentRowYWeight 5 := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent005A0 nativeSetupParent005Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent005A0 nativeSetupParent005Xi0 := by rfl
  have hl : (nativeSetupParent005Ops.drop 207).length=350 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent005Ops.take 207)).getD 0 (.const 0)=parentRowWeightedExpr parentRowYWeight 5 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent005Ops.take 207) (nativeSetupParent005Ops.drop 207) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent005FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent005Real]
  rw [hh,parent_row_weighted_expr_eval env (by rfl)]

/-- The exact depth-6 Y coefficient is its physical shell sum. -/
theorem parent_row_y_006 :
    nativeSetupParent006FieldsR.getD 16 0=parentRowWeightedClock parentRowYWeight 6 := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent006A0 nativeSetupParent006Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent006A0 nativeSetupParent006Xi0 := by rfl
  have hl : (nativeSetupParent006Ops.drop 238).length=350 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent006Ops.take 238)).getD 0 (.const 0)=parentRowWeightedExpr parentRowYWeight 6 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent006Ops.take 238) (nativeSetupParent006Ops.drop 238) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent006FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent006Real]
  rw [hh,parent_row_weighted_expr_eval env (by rfl)]

/-- The exact depth-7 Y coefficient is its physical shell sum. -/
theorem parent_row_y_007 :
    nativeSetupParent007FieldsR.getD 16 0=parentRowWeightedClock parentRowYWeight 7 := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent007A0 nativeSetupParent007Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent007A0 nativeSetupParent007Xi0 := by rfl
  have hl : (nativeSetupParent007Ops.drop 268).length=350 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent007Ops.take 268)).getD 0 (.const 0)=parentRowWeightedExpr parentRowYWeight 7 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent007Ops.take 268) (nativeSetupParent007Ops.drop 268) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent007FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent007Real]
  rw [hh,parent_row_weighted_expr_eval env (by rfl)]

/-- The exact depth-8 Y coefficient is its physical shell sum. -/
theorem parent_row_y_008 :
    nativeSetupParent008FieldsR.getD 16 0=parentRowWeightedClock parentRowYWeight 8 := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent008A0 nativeSetupParent008Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent008A0 nativeSetupParent008Xi0 := by rfl
  have hl : (nativeSetupParent008Ops.drop 299).length=350 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent008Ops.take 299)).getD 0 (.const 0)=parentRowWeightedExpr parentRowYWeight 8 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent008Ops.take 299) (nativeSetupParent008Ops.drop 299) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent008FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent008Real]
  rw [hh,parent_row_weighted_expr_eval env (by rfl)]

/-- The exact depth-9 Y coefficient is its physical shell sum. -/
theorem parent_row_y_009 :
    nativeSetupParent009FieldsR.getD 16 0=parentRowWeightedClock parentRowYWeight 9 := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent009A0 nativeSetupParent009Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent009A0 nativeSetupParent009Xi0 := by rfl
  have hl : (nativeSetupParent009Ops.drop 329).length=350 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent009Ops.take 329)).getD 0 (.const 0)=parentRowWeightedExpr parentRowYWeight 9 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent009Ops.take 329) (nativeSetupParent009Ops.drop 329) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent009FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent009Real]
  rw [hh,parent_row_weighted_expr_eval env (by rfl)]

/-- The exact depth-10 Y coefficient is its physical shell sum. -/
theorem parent_row_y_010 :
    nativeSetupParent010FieldsR.getD 16 0=parentRowWeightedClock parentRowYWeight 10 := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent010A0 nativeSetupParent010Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent010A0 nativeSetupParent010Xi0 := by rfl
  have hl : (nativeSetupParent010Ops.drop 360).length=350 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent010Ops.take 360)).getD 0 (.const 0)=parentRowWeightedExpr parentRowYWeight 10 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent010Ops.take 360) (nativeSetupParent010Ops.drop 360) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent010FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent010Real]
  rw [hh,parent_row_weighted_expr_eval env (by rfl)]

/-- The exact depth-11 Y coefficient is its physical shell sum. -/
theorem parent_row_y_011 :
    nativeSetupParent011FieldsR.getD 16 0=parentRowWeightedClock parentRowYWeight 11 := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent011A0 nativeSetupParent011Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent011A0 nativeSetupParent011Xi0 := by rfl
  have hl : (nativeSetupParent011Ops.drop 390).length=350 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent011Ops.take 390)).getD 0 (.const 0)=parentRowWeightedExpr parentRowYWeight 11 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent011Ops.take 390) (nativeSetupParent011Ops.drop 390) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent011FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent011Real]
  rw [hh,parent_row_weighted_expr_eval env (by rfl)]

/-- The exact depth-12 Y coefficient is its physical shell sum. -/
theorem parent_row_y_012 :
    nativeSetupParent012FieldsR.getD 16 0=parentRowWeightedClock parentRowYWeight 12 := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent012A0 nativeSetupParent012Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent012A0 nativeSetupParent012Xi0 := by rfl
  have hl : (nativeSetupParent012Ops.drop 421).length=350 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent012Ops.take 421)).getD 0 (.const 0)=parentRowWeightedExpr parentRowYWeight 12 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent012Ops.take 421) (nativeSetupParent012Ops.drop 421) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent012FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent012Real]
  rw [hh,parent_row_weighted_expr_eval env (by rfl)]

/-- The exact depth-13 Y coefficient is its physical shell sum. -/
theorem parent_row_y_013 :
    nativeSetupParent013FieldsR.getD 16 0=parentRowWeightedClock parentRowYWeight 13 := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent013A0 nativeSetupParent013Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent013A0 nativeSetupParent013Xi0 := by rfl
  have hl : (nativeSetupParent013Ops.drop 451).length=350 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent013Ops.take 451)).getD 0 (.const 0)=parentRowWeightedExpr parentRowYWeight 13 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent013Ops.take 451) (nativeSetupParent013Ops.drop 451) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent013FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent013Real]
  rw [hh,parent_row_weighted_expr_eval env (by rfl)]

/-- The exact depth-14 Y coefficient is its physical shell sum. -/
theorem parent_row_y_014 :
    nativeSetupParent014FieldsR.getD 16 0=parentRowWeightedClock parentRowYWeight 14 := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent014A0 nativeSetupParent014Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent014A0 nativeSetupParent014Xi0 := by rfl
  have hl : (nativeSetupParent014Ops.drop 482).length=350 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent014Ops.take 482)).getD 0 (.const 0)=parentRowWeightedExpr parentRowYWeight 14 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent014Ops.take 482) (nativeSetupParent014Ops.drop 482) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent014FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent014Real]
  rw [hh,parent_row_weighted_expr_eval env (by rfl)]

/-- The exact depth-15 Y coefficient is its physical shell sum. -/
theorem parent_row_y_015 :
    nativeSetupParent015FieldsR.getD 16 0=parentRowWeightedClock parentRowYWeight 15 := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent015A0 nativeSetupParent015Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent015A0 nativeSetupParent015Xi0 := by rfl
  have hl : (nativeSetupParent015Ops.drop 512).length=350 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent015Ops.take 512)).getD 0 (.const 0)=parentRowWeightedExpr parentRowYWeight 15 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent015Ops.take 512) (nativeSetupParent015Ops.drop 512) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent015FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent015Real]
  rw [hh,parent_row_weighted_expr_eval env (by rfl)]

/-- The exact depth-16 Y coefficient is its physical shell sum. -/
theorem parent_row_y_016 :
    nativeSetupParent016FieldsR.getD 16 0=parentRowWeightedClock parentRowYWeight 16 := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent016A0 nativeSetupParent016Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent016A0 nativeSetupParent016Xi0 := by rfl
  have hl : (nativeSetupParent016Ops.drop 543).length=350 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent016Ops.take 543)).getD 0 (.const 0)=parentRowWeightedExpr parentRowYWeight 16 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent016Ops.take 543) (nativeSetupParent016Ops.drop 543) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent016FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent016Real]
  rw [hh,parent_row_weighted_expr_eval env (by rfl)]

end
end ASDExplicitGamma.Native
