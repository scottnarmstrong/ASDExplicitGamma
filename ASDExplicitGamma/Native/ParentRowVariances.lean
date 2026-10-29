module

public import ASDExplicitGamma.Native.ParentRowVarianceExpr
public import ASDExplicitGamma.Native.ParentRowCertificates

/-! The literal sixteen stored variances are their physical finite shell sums. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native Numerics.Mirror
noncomputable section

/-- The depth-1 variance is exactly the full source shell sum. -/
theorem parent_row_variance_001 :
    nativeSetupParent001FieldsR.getD 0 0=parentRowVarianceClock 1 := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent001A0 nativeSetupParent001Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent001A0 nativeSetupParent001Xi0 := by rfl
  have hl : (nativeSetupParent001Ops.drop 26).length=419 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent001Ops.take 26)).getD 0 (.const 0)=parentRowVarianceExpr 1 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent001Ops.take 26) (nativeSetupParent001Ops.drop 26) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent001FieldsR,List.getD_cons_zero,nativeSetupParent001Real]
  rw [hh,parent_row_variance_expr_eval env (by rfl)]

/-- The depth-2 variance is exactly the full source shell sum. -/
theorem parent_row_variance_002 :
    nativeSetupParent002FieldsR.getD 0 0=parentRowVarianceClock 2 := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent002A0 nativeSetupParent002Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent002A0 nativeSetupParent002Xi0 := by rfl
  have hl : (nativeSetupParent002Ops.drop 31).length=442 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent002Ops.take 31)).getD 0 (.const 0)=parentRowVarianceExpr 2 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent002Ops.take 31) (nativeSetupParent002Ops.drop 31) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent002FieldsR,List.getD_cons_zero,nativeSetupParent002Real]
  rw [hh,parent_row_variance_expr_eval env (by rfl)]

/-- The depth-3 variance is exactly the full source shell sum. -/
theorem parent_row_variance_003 :
    nativeSetupParent003FieldsR.getD 0 0=parentRowVarianceClock 3 := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent003A0 nativeSetupParent003Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent003A0 nativeSetupParent003Xi0 := by rfl
  have hl : (nativeSetupParent003Ops.drop 36).length=465 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent003Ops.take 36)).getD 0 (.const 0)=parentRowVarianceExpr 3 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent003Ops.take 36) (nativeSetupParent003Ops.drop 36) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent003FieldsR,List.getD_cons_zero,nativeSetupParent003Real]
  rw [hh,parent_row_variance_expr_eval env (by rfl)]

/-- The depth-4 variance is exactly the full source shell sum. -/
theorem parent_row_variance_004 :
    nativeSetupParent004FieldsR.getD 0 0=parentRowVarianceClock 4 := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent004A0 nativeSetupParent004Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent004A0 nativeSetupParent004Xi0 := by rfl
  have hl : (nativeSetupParent004Ops.drop 41).length=488 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent004Ops.take 41)).getD 0 (.const 0)=parentRowVarianceExpr 4 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent004Ops.take 41) (nativeSetupParent004Ops.drop 41) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent004FieldsR,List.getD_cons_zero,nativeSetupParent004Real]
  rw [hh,parent_row_variance_expr_eval env (by rfl)]

/-- The depth-5 variance is exactly the full source shell sum. -/
theorem parent_row_variance_005 :
    nativeSetupParent005FieldsR.getD 0 0=parentRowVarianceClock 5 := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent005A0 nativeSetupParent005Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent005A0 nativeSetupParent005Xi0 := by rfl
  have hl : (nativeSetupParent005Ops.drop 46).length=511 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent005Ops.take 46)).getD 0 (.const 0)=parentRowVarianceExpr 5 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent005Ops.take 46) (nativeSetupParent005Ops.drop 46) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent005FieldsR,List.getD_cons_zero,nativeSetupParent005Real]
  rw [hh,parent_row_variance_expr_eval env (by rfl)]

/-- The depth-6 variance is exactly the full source shell sum. -/
theorem parent_row_variance_006 :
    nativeSetupParent006FieldsR.getD 0 0=parentRowVarianceClock 6 := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent006A0 nativeSetupParent006Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent006A0 nativeSetupParent006Xi0 := by rfl
  have hl : (nativeSetupParent006Ops.drop 51).length=537 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent006Ops.take 51)).getD 0 (.const 0)=parentRowVarianceExpr 6 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent006Ops.take 51) (nativeSetupParent006Ops.drop 51) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent006FieldsR,List.getD_cons_zero,nativeSetupParent006Real]
  rw [hh,parent_row_variance_expr_eval env (by rfl)]

/-- The depth-7 variance is exactly the full source shell sum. -/
theorem parent_row_variance_007 :
    nativeSetupParent007FieldsR.getD 0 0=parentRowVarianceClock 7 := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent007A0 nativeSetupParent007Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent007A0 nativeSetupParent007Xi0 := by rfl
  have hl : (nativeSetupParent007Ops.drop 56).length=562 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent007Ops.take 56)).getD 0 (.const 0)=parentRowVarianceExpr 7 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent007Ops.take 56) (nativeSetupParent007Ops.drop 56) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent007FieldsR,List.getD_cons_zero,nativeSetupParent007Real]
  rw [hh,parent_row_variance_expr_eval env (by rfl)]

/-- The depth-8 variance is exactly the full source shell sum. -/
theorem parent_row_variance_008 :
    nativeSetupParent008FieldsR.getD 0 0=parentRowVarianceClock 8 := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent008A0 nativeSetupParent008Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent008A0 nativeSetupParent008Xi0 := by rfl
  have hl : (nativeSetupParent008Ops.drop 61).length=588 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent008Ops.take 61)).getD 0 (.const 0)=parentRowVarianceExpr 8 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent008Ops.take 61) (nativeSetupParent008Ops.drop 61) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent008FieldsR,List.getD_cons_zero,nativeSetupParent008Real]
  rw [hh,parent_row_variance_expr_eval env (by rfl)]

/-- The depth-9 variance is exactly the full source shell sum. -/
theorem parent_row_variance_009 :
    nativeSetupParent009FieldsR.getD 0 0=parentRowVarianceClock 9 := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent009A0 nativeSetupParent009Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent009A0 nativeSetupParent009Xi0 := by rfl
  have hl : (nativeSetupParent009Ops.drop 66).length=613 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent009Ops.take 66)).getD 0 (.const 0)=parentRowVarianceExpr 9 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent009Ops.take 66) (nativeSetupParent009Ops.drop 66) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent009FieldsR,List.getD_cons_zero,nativeSetupParent009Real]
  rw [hh,parent_row_variance_expr_eval env (by rfl)]

/-- The depth-10 variance is exactly the full source shell sum. -/
theorem parent_row_variance_010 :
    nativeSetupParent010FieldsR.getD 0 0=parentRowVarianceClock 10 := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent010A0 nativeSetupParent010Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent010A0 nativeSetupParent010Xi0 := by rfl
  have hl : (nativeSetupParent010Ops.drop 71).length=639 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent010Ops.take 71)).getD 0 (.const 0)=parentRowVarianceExpr 10 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent010Ops.take 71) (nativeSetupParent010Ops.drop 71) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent010FieldsR,List.getD_cons_zero,nativeSetupParent010Real]
  rw [hh,parent_row_variance_expr_eval env (by rfl)]

/-- The depth-11 variance is exactly the full source shell sum. -/
theorem parent_row_variance_011 :
    nativeSetupParent011FieldsR.getD 0 0=parentRowVarianceClock 11 := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent011A0 nativeSetupParent011Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent011A0 nativeSetupParent011Xi0 := by rfl
  have hl : (nativeSetupParent011Ops.drop 76).length=664 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent011Ops.take 76)).getD 0 (.const 0)=parentRowVarianceExpr 11 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent011Ops.take 76) (nativeSetupParent011Ops.drop 76) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent011FieldsR,List.getD_cons_zero,nativeSetupParent011Real]
  rw [hh,parent_row_variance_expr_eval env (by rfl)]

/-- The depth-12 variance is exactly the full source shell sum. -/
theorem parent_row_variance_012 :
    nativeSetupParent012FieldsR.getD 0 0=parentRowVarianceClock 12 := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent012A0 nativeSetupParent012Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent012A0 nativeSetupParent012Xi0 := by rfl
  have hl : (nativeSetupParent012Ops.drop 81).length=690 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent012Ops.take 81)).getD 0 (.const 0)=parentRowVarianceExpr 12 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent012Ops.take 81) (nativeSetupParent012Ops.drop 81) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent012FieldsR,List.getD_cons_zero,nativeSetupParent012Real]
  rw [hh,parent_row_variance_expr_eval env (by rfl)]

/-- The depth-13 variance is exactly the full source shell sum. -/
theorem parent_row_variance_013 :
    nativeSetupParent013FieldsR.getD 0 0=parentRowVarianceClock 13 := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent013A0 nativeSetupParent013Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent013A0 nativeSetupParent013Xi0 := by rfl
  have hl : (nativeSetupParent013Ops.drop 86).length=715 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent013Ops.take 86)).getD 0 (.const 0)=parentRowVarianceExpr 13 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent013Ops.take 86) (nativeSetupParent013Ops.drop 86) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent013FieldsR,List.getD_cons_zero,nativeSetupParent013Real]
  rw [hh,parent_row_variance_expr_eval env (by rfl)]

/-- The depth-14 variance is exactly the full source shell sum. -/
theorem parent_row_variance_014 :
    nativeSetupParent014FieldsR.getD 0 0=parentRowVarianceClock 14 := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent014A0 nativeSetupParent014Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent014A0 nativeSetupParent014Xi0 := by rfl
  have hl : (nativeSetupParent014Ops.drop 91).length=741 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent014Ops.take 91)).getD 0 (.const 0)=parentRowVarianceExpr 14 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent014Ops.take 91) (nativeSetupParent014Ops.drop 91) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent014FieldsR,List.getD_cons_zero,nativeSetupParent014Real]
  rw [hh,parent_row_variance_expr_eval env (by rfl)]

/-- The depth-15 variance is exactly the full source shell sum. -/
theorem parent_row_variance_015 :
    nativeSetupParent015FieldsR.getD 0 0=parentRowVarianceClock 15 := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent015A0 nativeSetupParent015Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent015A0 nativeSetupParent015Xi0 := by rfl
  have hl : (nativeSetupParent015Ops.drop 96).length=766 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent015Ops.take 96)).getD 0 (.const 0)=parentRowVarianceExpr 15 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent015Ops.take 96) (nativeSetupParent015Ops.drop 96) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent015FieldsR,List.getD_cons_zero,nativeSetupParent015Real]
  rw [hh,parent_row_variance_expr_eval env (by rfl)]

/-- The depth-16 variance is exactly the full source shell sum. -/
theorem parent_row_variance_016 :
    nativeSetupParent016FieldsR.getD 0 0=parentRowVarianceClock 16 := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent016A0 nativeSetupParent016Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent016A0 nativeSetupParent016Xi0 := by rfl
  have hl : (nativeSetupParent016Ops.drop 101).length=792 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent016Ops.take 101)).getD 0 (.const 0)=parentRowVarianceExpr 16 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent016Ops.take 101) (nativeSetupParent016Ops.drop 101) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent016FieldsR,List.getD_cons_zero,nativeSetupParent016Real]
  rw [hh,parent_row_variance_expr_eval env (by rfl)]

end
end ASDExplicitGamma.Native
