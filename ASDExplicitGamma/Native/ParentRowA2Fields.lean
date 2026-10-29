module

public import ASDExplicitGamma.Native.ParentRowWeightedClocks
public import ASDExplicitGamma.Native.ParentRowCertificates

/-! Exact weighted parent coefficients in all sixteen certified source setups. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native Numerics.Mirror
noncomputable section

/-- The exact depth-1 A2 coefficient is its physical shell sum. -/
theorem parent_row_a2_001 :
    nativeSetupParent001FieldsR.getD 1 0=parentRowWeightedClock parentRowA2Weight 1 := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent001A0 nativeSetupParent001Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent001A0 nativeSetupParent001Xi0 := by rfl
  have hl : (nativeSetupParent001Ops.drop 29).length=416 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent001Ops.take 29)).getD 0 (.const 0)=parentRowWeightedExpr parentRowA2Weight 1 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent001Ops.take 29) (nativeSetupParent001Ops.drop 29) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent001FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent001Real]
  rw [hh,parent_row_weighted_expr_eval env (by rfl)]

/-- The exact depth-2 A2 coefficient is its physical shell sum. -/
theorem parent_row_a2_002 :
    nativeSetupParent002FieldsR.getD 1 0=parentRowWeightedClock parentRowA2Weight 2 := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent002A0 nativeSetupParent002Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent002A0 nativeSetupParent002Xi0 := by rfl
  have hl : (nativeSetupParent002Ops.drop 37).length=436 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent002Ops.take 37)).getD 0 (.const 0)=parentRowWeightedExpr parentRowA2Weight 2 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent002Ops.take 37) (nativeSetupParent002Ops.drop 37) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent002FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent002Real]
  rw [hh,parent_row_weighted_expr_eval env (by rfl)]

/-- The exact depth-3 A2 coefficient is its physical shell sum. -/
theorem parent_row_a2_003 :
    nativeSetupParent003FieldsR.getD 1 0=parentRowWeightedClock parentRowA2Weight 3 := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent003A0 nativeSetupParent003Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent003A0 nativeSetupParent003Xi0 := by rfl
  have hl : (nativeSetupParent003Ops.drop 45).length=456 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent003Ops.take 45)).getD 0 (.const 0)=parentRowWeightedExpr parentRowA2Weight 3 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent003Ops.take 45) (nativeSetupParent003Ops.drop 45) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent003FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent003Real]
  rw [hh,parent_row_weighted_expr_eval env (by rfl)]

/-- The exact depth-4 A2 coefficient is its physical shell sum. -/
theorem parent_row_a2_004 :
    nativeSetupParent004FieldsR.getD 1 0=parentRowWeightedClock parentRowA2Weight 4 := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent004A0 nativeSetupParent004Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent004A0 nativeSetupParent004Xi0 := by rfl
  have hl : (nativeSetupParent004Ops.drop 53).length=476 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent004Ops.take 53)).getD 0 (.const 0)=parentRowWeightedExpr parentRowA2Weight 4 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent004Ops.take 53) (nativeSetupParent004Ops.drop 53) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent004FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent004Real]
  rw [hh,parent_row_weighted_expr_eval env (by rfl)]

/-- The exact depth-5 A2 coefficient is its physical shell sum. -/
theorem parent_row_a2_005 :
    nativeSetupParent005FieldsR.getD 1 0=parentRowWeightedClock parentRowA2Weight 5 := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent005A0 nativeSetupParent005Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent005A0 nativeSetupParent005Xi0 := by rfl
  have hl : (nativeSetupParent005Ops.drop 61).length=496 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent005Ops.take 61)).getD 0 (.const 0)=parentRowWeightedExpr parentRowA2Weight 5 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent005Ops.take 61) (nativeSetupParent005Ops.drop 61) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent005FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent005Real]
  rw [hh,parent_row_weighted_expr_eval env (by rfl)]

/-- The exact depth-6 A2 coefficient is its physical shell sum. -/
theorem parent_row_a2_006 :
    nativeSetupParent006FieldsR.getD 1 0=parentRowWeightedClock parentRowA2Weight 6 := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent006A0 nativeSetupParent006Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent006A0 nativeSetupParent006Xi0 := by rfl
  have hl : (nativeSetupParent006Ops.drop 69).length=519 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent006Ops.take 69)).getD 0 (.const 0)=parentRowWeightedExpr parentRowA2Weight 6 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent006Ops.take 69) (nativeSetupParent006Ops.drop 69) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent006FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent006Real]
  rw [hh,parent_row_weighted_expr_eval env (by rfl)]

/-- The exact depth-7 A2 coefficient is its physical shell sum. -/
theorem parent_row_a2_007 :
    nativeSetupParent007FieldsR.getD 1 0=parentRowWeightedClock parentRowA2Weight 7 := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent007A0 nativeSetupParent007Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent007A0 nativeSetupParent007Xi0 := by rfl
  have hl : (nativeSetupParent007Ops.drop 77).length=541 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent007Ops.take 77)).getD 0 (.const 0)=parentRowWeightedExpr parentRowA2Weight 7 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent007Ops.take 77) (nativeSetupParent007Ops.drop 77) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent007FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent007Real]
  rw [hh,parent_row_weighted_expr_eval env (by rfl)]

/-- The exact depth-8 A2 coefficient is its physical shell sum. -/
theorem parent_row_a2_008 :
    nativeSetupParent008FieldsR.getD 1 0=parentRowWeightedClock parentRowA2Weight 8 := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent008A0 nativeSetupParent008Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent008A0 nativeSetupParent008Xi0 := by rfl
  have hl : (nativeSetupParent008Ops.drop 85).length=564 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent008Ops.take 85)).getD 0 (.const 0)=parentRowWeightedExpr parentRowA2Weight 8 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent008Ops.take 85) (nativeSetupParent008Ops.drop 85) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent008FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent008Real]
  rw [hh,parent_row_weighted_expr_eval env (by rfl)]

/-- The exact depth-9 A2 coefficient is its physical shell sum. -/
theorem parent_row_a2_009 :
    nativeSetupParent009FieldsR.getD 1 0=parentRowWeightedClock parentRowA2Weight 9 := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent009A0 nativeSetupParent009Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent009A0 nativeSetupParent009Xi0 := by rfl
  have hl : (nativeSetupParent009Ops.drop 93).length=586 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent009Ops.take 93)).getD 0 (.const 0)=parentRowWeightedExpr parentRowA2Weight 9 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent009Ops.take 93) (nativeSetupParent009Ops.drop 93) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent009FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent009Real]
  rw [hh,parent_row_weighted_expr_eval env (by rfl)]

/-- The exact depth-10 A2 coefficient is its physical shell sum. -/
theorem parent_row_a2_010 :
    nativeSetupParent010FieldsR.getD 1 0=parentRowWeightedClock parentRowA2Weight 10 := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent010A0 nativeSetupParent010Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent010A0 nativeSetupParent010Xi0 := by rfl
  have hl : (nativeSetupParent010Ops.drop 101).length=609 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent010Ops.take 101)).getD 0 (.const 0)=parentRowWeightedExpr parentRowA2Weight 10 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent010Ops.take 101) (nativeSetupParent010Ops.drop 101) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent010FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent010Real]
  rw [hh,parent_row_weighted_expr_eval env (by rfl)]

/-- The exact depth-11 A2 coefficient is its physical shell sum. -/
theorem parent_row_a2_011 :
    nativeSetupParent011FieldsR.getD 1 0=parentRowWeightedClock parentRowA2Weight 11 := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent011A0 nativeSetupParent011Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent011A0 nativeSetupParent011Xi0 := by rfl
  have hl : (nativeSetupParent011Ops.drop 109).length=631 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent011Ops.take 109)).getD 0 (.const 0)=parentRowWeightedExpr parentRowA2Weight 11 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent011Ops.take 109) (nativeSetupParent011Ops.drop 109) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent011FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent011Real]
  rw [hh,parent_row_weighted_expr_eval env (by rfl)]

/-- The exact depth-12 A2 coefficient is its physical shell sum. -/
theorem parent_row_a2_012 :
    nativeSetupParent012FieldsR.getD 1 0=parentRowWeightedClock parentRowA2Weight 12 := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent012A0 nativeSetupParent012Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent012A0 nativeSetupParent012Xi0 := by rfl
  have hl : (nativeSetupParent012Ops.drop 117).length=654 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent012Ops.take 117)).getD 0 (.const 0)=parentRowWeightedExpr parentRowA2Weight 12 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent012Ops.take 117) (nativeSetupParent012Ops.drop 117) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent012FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent012Real]
  rw [hh,parent_row_weighted_expr_eval env (by rfl)]

/-- The exact depth-13 A2 coefficient is its physical shell sum. -/
theorem parent_row_a2_013 :
    nativeSetupParent013FieldsR.getD 1 0=parentRowWeightedClock parentRowA2Weight 13 := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent013A0 nativeSetupParent013Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent013A0 nativeSetupParent013Xi0 := by rfl
  have hl : (nativeSetupParent013Ops.drop 125).length=676 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent013Ops.take 125)).getD 0 (.const 0)=parentRowWeightedExpr parentRowA2Weight 13 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent013Ops.take 125) (nativeSetupParent013Ops.drop 125) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent013FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent013Real]
  rw [hh,parent_row_weighted_expr_eval env (by rfl)]

/-- The exact depth-14 A2 coefficient is its physical shell sum. -/
theorem parent_row_a2_014 :
    nativeSetupParent014FieldsR.getD 1 0=parentRowWeightedClock parentRowA2Weight 14 := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent014A0 nativeSetupParent014Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent014A0 nativeSetupParent014Xi0 := by rfl
  have hl : (nativeSetupParent014Ops.drop 133).length=699 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent014Ops.take 133)).getD 0 (.const 0)=parentRowWeightedExpr parentRowA2Weight 14 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent014Ops.take 133) (nativeSetupParent014Ops.drop 133) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent014FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent014Real]
  rw [hh,parent_row_weighted_expr_eval env (by rfl)]

/-- The exact depth-15 A2 coefficient is its physical shell sum. -/
theorem parent_row_a2_015 :
    nativeSetupParent015FieldsR.getD 1 0=parentRowWeightedClock parentRowA2Weight 15 := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent015A0 nativeSetupParent015Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent015A0 nativeSetupParent015Xi0 := by rfl
  have hl : (nativeSetupParent015Ops.drop 141).length=721 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent015Ops.take 141)).getD 0 (.const 0)=parentRowWeightedExpr parentRowA2Weight 15 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent015Ops.take 141) (nativeSetupParent015Ops.drop 141) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent015FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent015Real]
  rw [hh,parent_row_weighted_expr_eval env (by rfl)]

/-- The exact depth-16 A2 coefficient is its physical shell sum. -/
theorem parent_row_a2_016 :
    nativeSetupParent016FieldsR.getD 1 0=parentRowWeightedClock parentRowA2Weight 16 := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent016A0 nativeSetupParent016Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent016A0 nativeSetupParent016Xi0 := by rfl
  have hl : (nativeSetupParent016Ops.drop 149).length=744 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent016Ops.take 149)).getD 0 (.const 0)=parentRowWeightedExpr parentRowA2Weight 16 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent016Ops.take 149) (nativeSetupParent016Ops.drop 149) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent016FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent016Real]
  rw [hh,parent_row_weighted_expr_eval env (by rfl)]

end
end ASDExplicitGamma.Native
