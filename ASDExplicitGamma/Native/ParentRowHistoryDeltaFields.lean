module

public import ASDExplicitGamma.Native.ParentRowHistoryDeltaExpr
public import ASDExplicitGamma.Native.ParentRowCertificates

/-! Kernel-checked history drift expressions for all sixteen parent rows. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native Numerics.Mirror
noncomputable section

/-- Literal history drift at parent height 1. -/
theorem parent_row_delta_expr_001 :
    nativeSetupParent001FieldsR.getD 10 0=
      evalReal (fun i => (nativeSetupInputReal nativeSetupParent001A0 nativeSetupParent001Xi0).getD i 0)
        (parentRowHistoryDeltaExpr 1) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent001A0 nativeSetupParent001Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent001A0 nativeSetupParent001Xi0 := by rfl
  have hl : (nativeSetupParent001Ops.drop 268).length=177 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent001Ops.take 268)).getD 0 (.const 0)=parentRowHistoryDeltaExpr 1 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent001Ops.take 268) (nativeSetupParent001Ops.drop 268) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simpa only [nativeSetupParent001FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent001Real] using hh

/-- Literal history drift at parent height 2. -/
theorem parent_row_delta_expr_002 :
    nativeSetupParent002FieldsR.getD 10 0=
      evalReal (fun i => (nativeSetupInputReal nativeSetupParent002A0 nativeSetupParent002Xi0).getD i 0)
        (parentRowHistoryDeltaExpr 2) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent002A0 nativeSetupParent002Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent002A0 nativeSetupParent002Xi0 := by rfl
  have hl : (nativeSetupParent002Ops.drop 299).length=174 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent002Ops.take 299)).getD 0 (.const 0)=parentRowHistoryDeltaExpr 2 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent002Ops.take 299) (nativeSetupParent002Ops.drop 299) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simpa only [nativeSetupParent002FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent002Real] using hh

/-- Literal history drift at parent height 3. -/
theorem parent_row_delta_expr_003 :
    nativeSetupParent003FieldsR.getD 10 0=
      evalReal (fun i => (nativeSetupInputReal nativeSetupParent003A0 nativeSetupParent003Xi0).getD i 0)
        (parentRowHistoryDeltaExpr 3) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent003A0 nativeSetupParent003Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent003A0 nativeSetupParent003Xi0 := by rfl
  have hl : (nativeSetupParent003Ops.drop 327).length=174 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent003Ops.take 327)).getD 0 (.const 0)=parentRowHistoryDeltaExpr 3 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent003Ops.take 327) (nativeSetupParent003Ops.drop 327) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simpa only [nativeSetupParent003FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent003Real] using hh

/-- Literal history drift at parent height 4. -/
theorem parent_row_delta_expr_004 :
    nativeSetupParent004FieldsR.getD 10 0=
      evalReal (fun i => (nativeSetupInputReal nativeSetupParent004A0 nativeSetupParent004Xi0).getD i 0)
        (parentRowHistoryDeltaExpr 4) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent004A0 nativeSetupParent004Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent004A0 nativeSetupParent004Xi0 := by rfl
  have hl : (nativeSetupParent004Ops.drop 355).length=174 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent004Ops.take 355)).getD 0 (.const 0)=parentRowHistoryDeltaExpr 4 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent004Ops.take 355) (nativeSetupParent004Ops.drop 355) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simpa only [nativeSetupParent004FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent004Real] using hh

/-- Literal history drift at parent height 5. -/
theorem parent_row_delta_expr_005 :
    nativeSetupParent005FieldsR.getD 10 0=
      evalReal (fun i => (nativeSetupInputReal nativeSetupParent005A0 nativeSetupParent005Xi0).getD i 0)
        (parentRowHistoryDeltaExpr 5) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent005A0 nativeSetupParent005Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent005A0 nativeSetupParent005Xi0 := by rfl
  have hl : (nativeSetupParent005Ops.drop 386).length=171 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent005Ops.take 386)).getD 0 (.const 0)=parentRowHistoryDeltaExpr 5 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent005Ops.take 386) (nativeSetupParent005Ops.drop 386) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simpa only [nativeSetupParent005FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent005Real] using hh

/-- Literal history drift at parent height 6. -/
theorem parent_row_delta_expr_006 :
    nativeSetupParent006FieldsR.getD 10 0=
      evalReal (fun i => (nativeSetupInputReal nativeSetupParent006A0 nativeSetupParent006Xi0).getD i 0)
        (parentRowHistoryDeltaExpr 6) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent006A0 nativeSetupParent006Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent006A0 nativeSetupParent006Xi0 := by rfl
  have hl : (nativeSetupParent006Ops.drop 417).length=171 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent006Ops.take 417)).getD 0 (.const 0)=parentRowHistoryDeltaExpr 6 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent006Ops.take 417) (nativeSetupParent006Ops.drop 417) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simpa only [nativeSetupParent006FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent006Real] using hh

/-- Literal history drift at parent height 7. -/
theorem parent_row_delta_expr_007 :
    nativeSetupParent007FieldsR.getD 10 0=
      evalReal (fun i => (nativeSetupInputReal nativeSetupParent007A0 nativeSetupParent007Xi0).getD i 0)
        (parentRowHistoryDeltaExpr 7) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent007A0 nativeSetupParent007Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent007A0 nativeSetupParent007Xi0 := by rfl
  have hl : (nativeSetupParent007Ops.drop 447).length=171 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent007Ops.take 447)).getD 0 (.const 0)=parentRowHistoryDeltaExpr 7 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent007Ops.take 447) (nativeSetupParent007Ops.drop 447) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simpa only [nativeSetupParent007FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent007Real] using hh

/-- Literal history drift at parent height 8. -/
theorem parent_row_delta_expr_008 :
    nativeSetupParent008FieldsR.getD 10 0=
      evalReal (fun i => (nativeSetupInputReal nativeSetupParent008A0 nativeSetupParent008Xi0).getD i 0)
        (parentRowHistoryDeltaExpr 8) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent008A0 nativeSetupParent008Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent008A0 nativeSetupParent008Xi0 := by rfl
  have hl : (nativeSetupParent008Ops.drop 478).length=171 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent008Ops.take 478)).getD 0 (.const 0)=parentRowHistoryDeltaExpr 8 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent008Ops.take 478) (nativeSetupParent008Ops.drop 478) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simpa only [nativeSetupParent008FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent008Real] using hh

/-- Literal history drift at parent height 9. -/
theorem parent_row_delta_expr_009 :
    nativeSetupParent009FieldsR.getD 10 0=
      evalReal (fun i => (nativeSetupInputReal nativeSetupParent009A0 nativeSetupParent009Xi0).getD i 0)
        (parentRowHistoryDeltaExpr 9) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent009A0 nativeSetupParent009Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent009A0 nativeSetupParent009Xi0 := by rfl
  have hl : (nativeSetupParent009Ops.drop 508).length=171 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent009Ops.take 508)).getD 0 (.const 0)=parentRowHistoryDeltaExpr 9 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent009Ops.take 508) (nativeSetupParent009Ops.drop 508) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simpa only [nativeSetupParent009FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent009Real] using hh

/-- Literal history drift at parent height 10. -/
theorem parent_row_delta_expr_010 :
    nativeSetupParent010FieldsR.getD 10 0=
      evalReal (fun i => (nativeSetupInputReal nativeSetupParent010A0 nativeSetupParent010Xi0).getD i 0)
        (parentRowHistoryDeltaExpr 10) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent010A0 nativeSetupParent010Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent010A0 nativeSetupParent010Xi0 := by rfl
  have hl : (nativeSetupParent010Ops.drop 539).length=171 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent010Ops.take 539)).getD 0 (.const 0)=parentRowHistoryDeltaExpr 10 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent010Ops.take 539) (nativeSetupParent010Ops.drop 539) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simpa only [nativeSetupParent010FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent010Real] using hh

/-- Literal history drift at parent height 11. -/
theorem parent_row_delta_expr_011 :
    nativeSetupParent011FieldsR.getD 10 0=
      evalReal (fun i => (nativeSetupInputReal nativeSetupParent011A0 nativeSetupParent011Xi0).getD i 0)
        (parentRowHistoryDeltaExpr 11) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent011A0 nativeSetupParent011Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent011A0 nativeSetupParent011Xi0 := by rfl
  have hl : (nativeSetupParent011Ops.drop 569).length=171 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent011Ops.take 569)).getD 0 (.const 0)=parentRowHistoryDeltaExpr 11 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent011Ops.take 569) (nativeSetupParent011Ops.drop 569) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simpa only [nativeSetupParent011FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent011Real] using hh

/-- Literal history drift at parent height 12. -/
theorem parent_row_delta_expr_012 :
    nativeSetupParent012FieldsR.getD 10 0=
      evalReal (fun i => (nativeSetupInputReal nativeSetupParent012A0 nativeSetupParent012Xi0).getD i 0)
        (parentRowHistoryDeltaExpr 12) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent012A0 nativeSetupParent012Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent012A0 nativeSetupParent012Xi0 := by rfl
  have hl : (nativeSetupParent012Ops.drop 600).length=171 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent012Ops.take 600)).getD 0 (.const 0)=parentRowHistoryDeltaExpr 12 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent012Ops.take 600) (nativeSetupParent012Ops.drop 600) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simpa only [nativeSetupParent012FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent012Real] using hh

/-- Literal history drift at parent height 13. -/
theorem parent_row_delta_expr_013 :
    nativeSetupParent013FieldsR.getD 10 0=
      evalReal (fun i => (nativeSetupInputReal nativeSetupParent013A0 nativeSetupParent013Xi0).getD i 0)
        (parentRowHistoryDeltaExpr 13) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent013A0 nativeSetupParent013Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent013A0 nativeSetupParent013Xi0 := by rfl
  have hl : (nativeSetupParent013Ops.drop 630).length=171 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent013Ops.take 630)).getD 0 (.const 0)=parentRowHistoryDeltaExpr 13 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent013Ops.take 630) (nativeSetupParent013Ops.drop 630) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simpa only [nativeSetupParent013FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent013Real] using hh

/-- Literal history drift at parent height 14. -/
theorem parent_row_delta_expr_014 :
    nativeSetupParent014FieldsR.getD 10 0=
      evalReal (fun i => (nativeSetupInputReal nativeSetupParent014A0 nativeSetupParent014Xi0).getD i 0)
        (parentRowHistoryDeltaExpr 14) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent014A0 nativeSetupParent014Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent014A0 nativeSetupParent014Xi0 := by rfl
  have hl : (nativeSetupParent014Ops.drop 661).length=171 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent014Ops.take 661)).getD 0 (.const 0)=parentRowHistoryDeltaExpr 14 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent014Ops.take 661) (nativeSetupParent014Ops.drop 661) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simpa only [nativeSetupParent014FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent014Real] using hh

/-- Literal history drift at parent height 15. -/
theorem parent_row_delta_expr_015 :
    nativeSetupParent015FieldsR.getD 10 0=
      evalReal (fun i => (nativeSetupInputReal nativeSetupParent015A0 nativeSetupParent015Xi0).getD i 0)
        (parentRowHistoryDeltaExpr 15) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent015A0 nativeSetupParent015Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent015A0 nativeSetupParent015Xi0 := by rfl
  have hl : (nativeSetupParent015Ops.drop 691).length=171 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent015Ops.take 691)).getD 0 (.const 0)=parentRowHistoryDeltaExpr 15 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent015Ops.take 691) (nativeSetupParent015Ops.drop 691) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simpa only [nativeSetupParent015FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent015Real] using hh

/-- Literal history drift at parent height 16. -/
theorem parent_row_delta_expr_016 :
    nativeSetupParent016FieldsR.getD 10 0=
      evalReal (fun i => (nativeSetupInputReal nativeSetupParent016A0 nativeSetupParent016Xi0).getD i 0)
        (parentRowHistoryDeltaExpr 16) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent016A0 nativeSetupParent016Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent016A0 nativeSetupParent016Xi0 := by rfl
  have hl : (nativeSetupParent016Ops.drop 722).length=171 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent016Ops.take 722)).getD 0 (.const 0)=parentRowHistoryDeltaExpr 16 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent016Ops.take 722) (nativeSetupParent016Ops.drop 722) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simpa only [nativeSetupParent016FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent016Real] using hh

end
end ASDExplicitGamma.Native
