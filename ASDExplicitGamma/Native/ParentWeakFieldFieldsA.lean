module

public import ASDExplicitGamma.Native.ParentWeakFieldExpr
public import ASDExplicitGamma.Native.ParentRowCertificates

/-! Exact kernel-checked stored parent weak-slope fields. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native Numerics.Mirror
noncomputable section

/-- The depth-1 weak-slope field is exactly the common source expression. -/
theorem parent_weak_field_slope_001 :
    nativeSetupParent001FieldsR.getD 12 0=
      evalReal (fun i => (nativeSetupInputReal nativeSetupParent001A0 nativeSetupParent001Xi0).getD i 0)
        (parentWeakFieldSlopeExpr 1) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent001A0 nativeSetupParent001Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent001A0 nativeSetupParent001Xi0 := by rfl
  have hl : (nativeSetupParent001Ops.drop 417).length=28 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent001Ops.take 417)).getD 0 (.const 0)=parentWeakFieldSlopeExpr 1 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent001Ops.take 417) (nativeSetupParent001Ops.drop 417) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simpa only [nativeSetupParent001FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent001Real] using hh

/-- The depth-2 weak-slope field is exactly the common source expression. -/
theorem parent_weak_field_slope_002 :
    nativeSetupParent002FieldsR.getD 12 0=
      evalReal (fun i => (nativeSetupInputReal nativeSetupParent002A0 nativeSetupParent002Xi0).getD i 0)
        (parentWeakFieldSlopeExpr 2) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent002A0 nativeSetupParent002Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent002A0 nativeSetupParent002Xi0 := by rfl
  have hl : (nativeSetupParent002Ops.drop 445).length=28 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent002Ops.take 445)).getD 0 (.const 0)=parentWeakFieldSlopeExpr 2 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent002Ops.take 445) (nativeSetupParent002Ops.drop 445) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simpa only [nativeSetupParent002FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent002Real] using hh

/-- The depth-3 weak-slope field is exactly the common source expression. -/
theorem parent_weak_field_slope_003 :
    nativeSetupParent003FieldsR.getD 12 0=
      evalReal (fun i => (nativeSetupInputReal nativeSetupParent003A0 nativeSetupParent003Xi0).getD i 0)
        (parentWeakFieldSlopeExpr 3) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent003A0 nativeSetupParent003Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent003A0 nativeSetupParent003Xi0 := by rfl
  have hl : (nativeSetupParent003Ops.drop 473).length=28 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent003Ops.take 473)).getD 0 (.const 0)=parentWeakFieldSlopeExpr 3 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent003Ops.take 473) (nativeSetupParent003Ops.drop 473) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simpa only [nativeSetupParent003FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent003Real] using hh

/-- The depth-4 weak-slope field is exactly the common source expression. -/
theorem parent_weak_field_slope_004 :
    nativeSetupParent004FieldsR.getD 12 0=
      evalReal (fun i => (nativeSetupInputReal nativeSetupParent004A0 nativeSetupParent004Xi0).getD i 0)
        (parentWeakFieldSlopeExpr 4) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent004A0 nativeSetupParent004Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent004A0 nativeSetupParent004Xi0 := by rfl
  have hl : (nativeSetupParent004Ops.drop 501).length=28 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent004Ops.take 501)).getD 0 (.const 0)=parentWeakFieldSlopeExpr 4 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent004Ops.take 501) (nativeSetupParent004Ops.drop 501) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simpa only [nativeSetupParent004FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent004Real] using hh

/-- The depth-5 weak-slope field is exactly the common source expression. -/
theorem parent_weak_field_slope_005 :
    nativeSetupParent005FieldsR.getD 12 0=
      evalReal (fun i => (nativeSetupInputReal nativeSetupParent005A0 nativeSetupParent005Xi0).getD i 0)
        (parentWeakFieldSlopeExpr 5) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent005A0 nativeSetupParent005Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent005A0 nativeSetupParent005Xi0 := by rfl
  have hl : (nativeSetupParent005Ops.drop 529).length=28 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent005Ops.take 529)).getD 0 (.const 0)=parentWeakFieldSlopeExpr 5 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent005Ops.take 529) (nativeSetupParent005Ops.drop 529) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simpa only [nativeSetupParent005FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent005Real] using hh

/-- The depth-6 weak-slope field is exactly the common source expression. -/
theorem parent_weak_field_slope_006 :
    nativeSetupParent006FieldsR.getD 12 0=
      evalReal (fun i => (nativeSetupInputReal nativeSetupParent006A0 nativeSetupParent006Xi0).getD i 0)
        (parentWeakFieldSlopeExpr 6) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent006A0 nativeSetupParent006Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent006A0 nativeSetupParent006Xi0 := by rfl
  have hl : (nativeSetupParent006Ops.drop 560).length=28 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent006Ops.take 560)).getD 0 (.const 0)=parentWeakFieldSlopeExpr 6 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent006Ops.take 560) (nativeSetupParent006Ops.drop 560) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simpa only [nativeSetupParent006FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent006Real] using hh

/-- The depth-7 weak-slope field is exactly the common source expression. -/
theorem parent_weak_field_slope_007 :
    nativeSetupParent007FieldsR.getD 12 0=
      evalReal (fun i => (nativeSetupInputReal nativeSetupParent007A0 nativeSetupParent007Xi0).getD i 0)
        (parentWeakFieldSlopeExpr 7) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent007A0 nativeSetupParent007Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent007A0 nativeSetupParent007Xi0 := by rfl
  have hl : (nativeSetupParent007Ops.drop 590).length=28 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent007Ops.take 590)).getD 0 (.const 0)=parentWeakFieldSlopeExpr 7 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent007Ops.take 590) (nativeSetupParent007Ops.drop 590) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simpa only [nativeSetupParent007FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent007Real] using hh

/-- The depth-8 weak-slope field is exactly the common source expression. -/
theorem parent_weak_field_slope_008 :
    nativeSetupParent008FieldsR.getD 12 0=
      evalReal (fun i => (nativeSetupInputReal nativeSetupParent008A0 nativeSetupParent008Xi0).getD i 0)
        (parentWeakFieldSlopeExpr 8) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent008A0 nativeSetupParent008Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent008A0 nativeSetupParent008Xi0 := by rfl
  have hl : (nativeSetupParent008Ops.drop 621).length=28 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent008Ops.take 621)).getD 0 (.const 0)=parentWeakFieldSlopeExpr 8 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent008Ops.take 621) (nativeSetupParent008Ops.drop 621) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simpa only [nativeSetupParent008FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent008Real] using hh

end
end ASDExplicitGamma.Native
