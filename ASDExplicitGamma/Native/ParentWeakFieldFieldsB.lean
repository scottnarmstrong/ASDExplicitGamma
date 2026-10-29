module

public import ASDExplicitGamma.Native.ParentWeakFieldExpr
public import ASDExplicitGamma.Native.ParentRowCertificates

/-! Exact kernel-checked stored parent weak-slope fields. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native Numerics.Mirror
noncomputable section

/-- The depth-9 weak-slope field is exactly the common source expression. -/
theorem parent_weak_field_slope_009 :
    nativeSetupParent009FieldsR.getD 12 0=
      evalReal (fun i => (nativeSetupInputReal nativeSetupParent009A0 nativeSetupParent009Xi0).getD i 0)
        (parentWeakFieldSlopeExpr 9) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent009A0 nativeSetupParent009Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent009A0 nativeSetupParent009Xi0 := by rfl
  have hl : (nativeSetupParent009Ops.drop 651).length=28 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent009Ops.take 651)).getD 0 (.const 0)=parentWeakFieldSlopeExpr 9 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent009Ops.take 651) (nativeSetupParent009Ops.drop 651) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simpa only [nativeSetupParent009FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent009Real] using hh

/-- The depth-10 weak-slope field is exactly the common source expression. -/
theorem parent_weak_field_slope_010 :
    nativeSetupParent010FieldsR.getD 12 0=
      evalReal (fun i => (nativeSetupInputReal nativeSetupParent010A0 nativeSetupParent010Xi0).getD i 0)
        (parentWeakFieldSlopeExpr 10) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent010A0 nativeSetupParent010Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent010A0 nativeSetupParent010Xi0 := by rfl
  have hl : (nativeSetupParent010Ops.drop 682).length=28 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent010Ops.take 682)).getD 0 (.const 0)=parentWeakFieldSlopeExpr 10 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent010Ops.take 682) (nativeSetupParent010Ops.drop 682) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simpa only [nativeSetupParent010FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent010Real] using hh

/-- The depth-11 weak-slope field is exactly the common source expression. -/
theorem parent_weak_field_slope_011 :
    nativeSetupParent011FieldsR.getD 12 0=
      evalReal (fun i => (nativeSetupInputReal nativeSetupParent011A0 nativeSetupParent011Xi0).getD i 0)
        (parentWeakFieldSlopeExpr 11) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent011A0 nativeSetupParent011Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent011A0 nativeSetupParent011Xi0 := by rfl
  have hl : (nativeSetupParent011Ops.drop 712).length=28 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent011Ops.take 712)).getD 0 (.const 0)=parentWeakFieldSlopeExpr 11 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent011Ops.take 712) (nativeSetupParent011Ops.drop 712) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simpa only [nativeSetupParent011FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent011Real] using hh

/-- The depth-12 weak-slope field is exactly the common source expression. -/
theorem parent_weak_field_slope_012 :
    nativeSetupParent012FieldsR.getD 12 0=
      evalReal (fun i => (nativeSetupInputReal nativeSetupParent012A0 nativeSetupParent012Xi0).getD i 0)
        (parentWeakFieldSlopeExpr 12) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent012A0 nativeSetupParent012Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent012A0 nativeSetupParent012Xi0 := by rfl
  have hl : (nativeSetupParent012Ops.drop 743).length=28 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent012Ops.take 743)).getD 0 (.const 0)=parentWeakFieldSlopeExpr 12 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent012Ops.take 743) (nativeSetupParent012Ops.drop 743) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simpa only [nativeSetupParent012FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent012Real] using hh

/-- The depth-13 weak-slope field is exactly the common source expression. -/
theorem parent_weak_field_slope_013 :
    nativeSetupParent013FieldsR.getD 12 0=
      evalReal (fun i => (nativeSetupInputReal nativeSetupParent013A0 nativeSetupParent013Xi0).getD i 0)
        (parentWeakFieldSlopeExpr 13) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent013A0 nativeSetupParent013Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent013A0 nativeSetupParent013Xi0 := by rfl
  have hl : (nativeSetupParent013Ops.drop 773).length=28 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent013Ops.take 773)).getD 0 (.const 0)=parentWeakFieldSlopeExpr 13 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent013Ops.take 773) (nativeSetupParent013Ops.drop 773) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simpa only [nativeSetupParent013FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent013Real] using hh

/-- The depth-14 weak-slope field is exactly the common source expression. -/
theorem parent_weak_field_slope_014 :
    nativeSetupParent014FieldsR.getD 12 0=
      evalReal (fun i => (nativeSetupInputReal nativeSetupParent014A0 nativeSetupParent014Xi0).getD i 0)
        (parentWeakFieldSlopeExpr 14) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent014A0 nativeSetupParent014Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent014A0 nativeSetupParent014Xi0 := by rfl
  have hl : (nativeSetupParent014Ops.drop 804).length=28 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent014Ops.take 804)).getD 0 (.const 0)=parentWeakFieldSlopeExpr 14 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent014Ops.take 804) (nativeSetupParent014Ops.drop 804) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simpa only [nativeSetupParent014FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent014Real] using hh

/-- The depth-15 weak-slope field is exactly the common source expression. -/
theorem parent_weak_field_slope_015 :
    nativeSetupParent015FieldsR.getD 12 0=
      evalReal (fun i => (nativeSetupInputReal nativeSetupParent015A0 nativeSetupParent015Xi0).getD i 0)
        (parentWeakFieldSlopeExpr 15) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent015A0 nativeSetupParent015Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent015A0 nativeSetupParent015Xi0 := by rfl
  have hl : (nativeSetupParent015Ops.drop 834).length=28 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent015Ops.take 834)).getD 0 (.const 0)=parentWeakFieldSlopeExpr 15 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent015Ops.take 834) (nativeSetupParent015Ops.drop 834) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simpa only [nativeSetupParent015FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent015Real] using hh

/-- The depth-16 weak-slope field is exactly the common source expression. -/
theorem parent_weak_field_slope_016 :
    nativeSetupParent016FieldsR.getD 12 0=
      evalReal (fun i => (nativeSetupInputReal nativeSetupParent016A0 nativeSetupParent016Xi0).getD i 0)
        (parentWeakFieldSlopeExpr 16) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent016A0 nativeSetupParent016Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent016A0 nativeSetupParent016Xi0 := by rfl
  have hl : (nativeSetupParent016Ops.drop 865).length=28 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent016Ops.take 865)).getD 0 (.const 0)=parentWeakFieldSlopeExpr 16 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent016Ops.take 865) (nativeSetupParent016Ops.drop 865) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simpa only [nativeSetupParent016FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent016Real] using hh

end
end ASDExplicitGamma.Native
