module

public import ASDExplicitGamma.Native.ParentRowMeanSlopeExpr
public import ASDExplicitGamma.Native.ParentRowCertificates

/-! Kernel-checked identification of all sixteen stored parent mean slopes. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native Numerics.Mirror
noncomputable section

/-- The depth-1 stored slope is the exact common source expression. -/
theorem parent_row_mean_slope_001 :
    nativeSetupParent001FieldsR.getD 11 0=
      evalReal (fun i => (nativeSetupInputReal nativeSetupParent001A0 nativeSetupParent001Xi0).getD i 0)
        (parentRowMeanSlopeExpr 1) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent001A0 nativeSetupParent001Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent001A0 nativeSetupParent001Xi0 := by rfl
  have hl : (nativeSetupParent001Ops.drop 302).length=143 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent001Ops.take 302)).getD 0 (.const 0)=parentRowMeanSlopeExpr 1 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent001Ops.take 302) (nativeSetupParent001Ops.drop 302) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simpa only [nativeSetupParent001FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent001Real] using hh

/-- The depth-2 stored slope is the exact common source expression. -/
theorem parent_row_mean_slope_002 :
    nativeSetupParent002FieldsR.getD 11 0=
      evalReal (fun i => (nativeSetupInputReal nativeSetupParent002A0 nativeSetupParent002Xi0).getD i 0)
        (parentRowMeanSlopeExpr 2) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent002A0 nativeSetupParent002Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent002A0 nativeSetupParent002Xi0 := by rfl
  have hl : (nativeSetupParent002Ops.drop 333).length=140 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent002Ops.take 333)).getD 0 (.const 0)=parentRowMeanSlopeExpr 2 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent002Ops.take 333) (nativeSetupParent002Ops.drop 333) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simpa only [nativeSetupParent002FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent002Real] using hh

/-- The depth-3 stored slope is the exact common source expression. -/
theorem parent_row_mean_slope_003 :
    nativeSetupParent003FieldsR.getD 11 0=
      evalReal (fun i => (nativeSetupInputReal nativeSetupParent003A0 nativeSetupParent003Xi0).getD i 0)
        (parentRowMeanSlopeExpr 3) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent003A0 nativeSetupParent003Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent003A0 nativeSetupParent003Xi0 := by rfl
  have hl : (nativeSetupParent003Ops.drop 361).length=140 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent003Ops.take 361)).getD 0 (.const 0)=parentRowMeanSlopeExpr 3 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent003Ops.take 361) (nativeSetupParent003Ops.drop 361) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simpa only [nativeSetupParent003FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent003Real] using hh

/-- The depth-4 stored slope is the exact common source expression. -/
theorem parent_row_mean_slope_004 :
    nativeSetupParent004FieldsR.getD 11 0=
      evalReal (fun i => (nativeSetupInputReal nativeSetupParent004A0 nativeSetupParent004Xi0).getD i 0)
        (parentRowMeanSlopeExpr 4) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent004A0 nativeSetupParent004Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent004A0 nativeSetupParent004Xi0 := by rfl
  have hl : (nativeSetupParent004Ops.drop 389).length=140 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent004Ops.take 389)).getD 0 (.const 0)=parentRowMeanSlopeExpr 4 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent004Ops.take 389) (nativeSetupParent004Ops.drop 389) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simpa only [nativeSetupParent004FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent004Real] using hh

/-- The depth-5 stored slope is the exact common source expression. -/
theorem parent_row_mean_slope_005 :
    nativeSetupParent005FieldsR.getD 11 0=
      evalReal (fun i => (nativeSetupInputReal nativeSetupParent005A0 nativeSetupParent005Xi0).getD i 0)
        (parentRowMeanSlopeExpr 5) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent005A0 nativeSetupParent005Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent005A0 nativeSetupParent005Xi0 := by rfl
  have hl : (nativeSetupParent005Ops.drop 420).length=137 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent005Ops.take 420)).getD 0 (.const 0)=parentRowMeanSlopeExpr 5 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent005Ops.take 420) (nativeSetupParent005Ops.drop 420) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simpa only [nativeSetupParent005FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent005Real] using hh

/-- The depth-6 stored slope is the exact common source expression. -/
theorem parent_row_mean_slope_006 :
    nativeSetupParent006FieldsR.getD 11 0=
      evalReal (fun i => (nativeSetupInputReal nativeSetupParent006A0 nativeSetupParent006Xi0).getD i 0)
        (parentRowMeanSlopeExpr 6) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent006A0 nativeSetupParent006Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent006A0 nativeSetupParent006Xi0 := by rfl
  have hl : (nativeSetupParent006Ops.drop 451).length=137 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent006Ops.take 451)).getD 0 (.const 0)=parentRowMeanSlopeExpr 6 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent006Ops.take 451) (nativeSetupParent006Ops.drop 451) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simpa only [nativeSetupParent006FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent006Real] using hh

/-- The depth-7 stored slope is the exact common source expression. -/
theorem parent_row_mean_slope_007 :
    nativeSetupParent007FieldsR.getD 11 0=
      evalReal (fun i => (nativeSetupInputReal nativeSetupParent007A0 nativeSetupParent007Xi0).getD i 0)
        (parentRowMeanSlopeExpr 7) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent007A0 nativeSetupParent007Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent007A0 nativeSetupParent007Xi0 := by rfl
  have hl : (nativeSetupParent007Ops.drop 481).length=137 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent007Ops.take 481)).getD 0 (.const 0)=parentRowMeanSlopeExpr 7 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent007Ops.take 481) (nativeSetupParent007Ops.drop 481) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simpa only [nativeSetupParent007FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent007Real] using hh

/-- The depth-8 stored slope is the exact common source expression. -/
theorem parent_row_mean_slope_008 :
    nativeSetupParent008FieldsR.getD 11 0=
      evalReal (fun i => (nativeSetupInputReal nativeSetupParent008A0 nativeSetupParent008Xi0).getD i 0)
        (parentRowMeanSlopeExpr 8) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent008A0 nativeSetupParent008Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent008A0 nativeSetupParent008Xi0 := by rfl
  have hl : (nativeSetupParent008Ops.drop 512).length=137 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent008Ops.take 512)).getD 0 (.const 0)=parentRowMeanSlopeExpr 8 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent008Ops.take 512) (nativeSetupParent008Ops.drop 512) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simpa only [nativeSetupParent008FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent008Real] using hh

/-- The depth-9 stored slope is the exact common source expression. -/
theorem parent_row_mean_slope_009 :
    nativeSetupParent009FieldsR.getD 11 0=
      evalReal (fun i => (nativeSetupInputReal nativeSetupParent009A0 nativeSetupParent009Xi0).getD i 0)
        (parentRowMeanSlopeExpr 9) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent009A0 nativeSetupParent009Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent009A0 nativeSetupParent009Xi0 := by rfl
  have hl : (nativeSetupParent009Ops.drop 542).length=137 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent009Ops.take 542)).getD 0 (.const 0)=parentRowMeanSlopeExpr 9 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent009Ops.take 542) (nativeSetupParent009Ops.drop 542) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simpa only [nativeSetupParent009FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent009Real] using hh

/-- The depth-10 stored slope is the exact common source expression. -/
theorem parent_row_mean_slope_010 :
    nativeSetupParent010FieldsR.getD 11 0=
      evalReal (fun i => (nativeSetupInputReal nativeSetupParent010A0 nativeSetupParent010Xi0).getD i 0)
        (parentRowMeanSlopeExpr 10) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent010A0 nativeSetupParent010Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent010A0 nativeSetupParent010Xi0 := by rfl
  have hl : (nativeSetupParent010Ops.drop 573).length=137 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent010Ops.take 573)).getD 0 (.const 0)=parentRowMeanSlopeExpr 10 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent010Ops.take 573) (nativeSetupParent010Ops.drop 573) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simpa only [nativeSetupParent010FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent010Real] using hh

/-- The depth-11 stored slope is the exact common source expression. -/
theorem parent_row_mean_slope_011 :
    nativeSetupParent011FieldsR.getD 11 0=
      evalReal (fun i => (nativeSetupInputReal nativeSetupParent011A0 nativeSetupParent011Xi0).getD i 0)
        (parentRowMeanSlopeExpr 11) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent011A0 nativeSetupParent011Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent011A0 nativeSetupParent011Xi0 := by rfl
  have hl : (nativeSetupParent011Ops.drop 603).length=137 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent011Ops.take 603)).getD 0 (.const 0)=parentRowMeanSlopeExpr 11 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent011Ops.take 603) (nativeSetupParent011Ops.drop 603) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simpa only [nativeSetupParent011FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent011Real] using hh

/-- The depth-12 stored slope is the exact common source expression. -/
theorem parent_row_mean_slope_012 :
    nativeSetupParent012FieldsR.getD 11 0=
      evalReal (fun i => (nativeSetupInputReal nativeSetupParent012A0 nativeSetupParent012Xi0).getD i 0)
        (parentRowMeanSlopeExpr 12) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent012A0 nativeSetupParent012Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent012A0 nativeSetupParent012Xi0 := by rfl
  have hl : (nativeSetupParent012Ops.drop 634).length=137 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent012Ops.take 634)).getD 0 (.const 0)=parentRowMeanSlopeExpr 12 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent012Ops.take 634) (nativeSetupParent012Ops.drop 634) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simpa only [nativeSetupParent012FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent012Real] using hh

/-- The depth-13 stored slope is the exact common source expression. -/
theorem parent_row_mean_slope_013 :
    nativeSetupParent013FieldsR.getD 11 0=
      evalReal (fun i => (nativeSetupInputReal nativeSetupParent013A0 nativeSetupParent013Xi0).getD i 0)
        (parentRowMeanSlopeExpr 13) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent013A0 nativeSetupParent013Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent013A0 nativeSetupParent013Xi0 := by rfl
  have hl : (nativeSetupParent013Ops.drop 664).length=137 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent013Ops.take 664)).getD 0 (.const 0)=parentRowMeanSlopeExpr 13 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent013Ops.take 664) (nativeSetupParent013Ops.drop 664) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simpa only [nativeSetupParent013FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent013Real] using hh

/-- The depth-14 stored slope is the exact common source expression. -/
theorem parent_row_mean_slope_014 :
    nativeSetupParent014FieldsR.getD 11 0=
      evalReal (fun i => (nativeSetupInputReal nativeSetupParent014A0 nativeSetupParent014Xi0).getD i 0)
        (parentRowMeanSlopeExpr 14) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent014A0 nativeSetupParent014Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent014A0 nativeSetupParent014Xi0 := by rfl
  have hl : (nativeSetupParent014Ops.drop 695).length=137 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent014Ops.take 695)).getD 0 (.const 0)=parentRowMeanSlopeExpr 14 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent014Ops.take 695) (nativeSetupParent014Ops.drop 695) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simpa only [nativeSetupParent014FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent014Real] using hh

/-- The depth-15 stored slope is the exact common source expression. -/
theorem parent_row_mean_slope_015 :
    nativeSetupParent015FieldsR.getD 11 0=
      evalReal (fun i => (nativeSetupInputReal nativeSetupParent015A0 nativeSetupParent015Xi0).getD i 0)
        (parentRowMeanSlopeExpr 15) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent015A0 nativeSetupParent015Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent015A0 nativeSetupParent015Xi0 := by rfl
  have hl : (nativeSetupParent015Ops.drop 725).length=137 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent015Ops.take 725)).getD 0 (.const 0)=parentRowMeanSlopeExpr 15 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent015Ops.take 725) (nativeSetupParent015Ops.drop 725) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simpa only [nativeSetupParent015FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent015Real] using hh

/-- The depth-16 stored slope is the exact common source expression. -/
theorem parent_row_mean_slope_016 :
    nativeSetupParent016FieldsR.getD 11 0=
      evalReal (fun i => (nativeSetupInputReal nativeSetupParent016A0 nativeSetupParent016Xi0).getD i 0)
        (parentRowMeanSlopeExpr 16) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent016A0 nativeSetupParent016Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent016A0 nativeSetupParent016Xi0 := by rfl
  have hl : (nativeSetupParent016Ops.drop 756).length=137 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent016Ops.take 756)).getD 0 (.const 0)=parentRowMeanSlopeExpr 16 := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent016Ops.take 756) (nativeSetupParent016Ops.drop 756) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simpa only [nativeSetupParent016FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent016Real] using hh

end
end ASDExplicitGamma.Native
