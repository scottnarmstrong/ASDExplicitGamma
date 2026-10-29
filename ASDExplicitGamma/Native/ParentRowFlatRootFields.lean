module

public import ASDExplicitGamma.Native.ParentRowWeightedFields

/-! Exact aggregate flat-energy roots in the parent panel programs. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native Numerics.Mirror
noncomputable section

/-- Source syntax for the joint flat root or the complete Dirichlet root. -/
def parentRowFlatRootExpr (height : ℕ) (joint : Bool) : Expr :=
  if joint then .sqrt (.mul (parentRowVarianceExpr height) (.const 2))
  else .sqrt (parentRowWeightedExpr parentRowYWeight height)

/-- Real interpretation of the two aggregate flat-energy roots. -/
def parentRowFlatRootValue (height : ℕ) (joint : Bool) : ℝ :=
  if joint then Real.sqrt (2*parentRowVarianceClock height)
  else Real.sqrt (parentRowWeightedClock parentRowYWeight height)

/-- Exact real meaning of the aggregate root syntax. -/
theorem parent_row_flat_root_expr_eval (env : ℕ → ℝ)
    (hlog : env 2=Real.log 3) (height : ℕ) (joint : Bool) :
    evalReal env (parentRowFlatRootExpr height joint)=parentRowFlatRootValue height joint := by
  cases joint <;> simp only [parentRowFlatRootExpr,parentRowFlatRootValue,
    Bool.false_eq_true,ite_false,ite_true,evalReal,parent_row_variance_expr_eval env hlog,
    parent_row_weighted_expr_eval env hlog,Rat.cast_ofNat,mul_comm]

/-- Exact joint root at parent height 1. -/
theorem parent_row_flat_root_joint_001 :
    nativeSetupParent001FieldsR.getD 8 0=parentRowFlatRootValue 1 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent001A0 nativeSetupParent001Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent001A0 nativeSetupParent001Xi0 := by rfl
  have hl : (nativeSetupParent001Ops.drop 101).length=344 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent001Ops.take 101)).getD 0 (.const 0)=parentRowFlatRootExpr 1 true := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent001Ops.take 101) (nativeSetupParent001Ops.drop 101) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_flat_root_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent001FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent001Real] using hh

/-- Exact dirichlet root at parent height 1. -/
theorem parent_row_flat_root_dirichlet_001 :
    nativeSetupParent001FieldsR.getD 9 0=parentRowFlatRootValue 1 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent001A0 nativeSetupParent001Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent001A0 nativeSetupParent001Xi0 := by rfl
  have hl : (nativeSetupParent001Ops.drop 102).length=343 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent001Ops.take 102)).getD 0 (.const 0)=parentRowFlatRootExpr 1 false := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent001Ops.take 102) (nativeSetupParent001Ops.drop 102) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_flat_root_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent001FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent001Real] using hh

/-- Exact joint root at parent height 2. -/
theorem parent_row_flat_root_joint_002 :
    nativeSetupParent002FieldsR.getD 8 0=parentRowFlatRootValue 2 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent002A0 nativeSetupParent002Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent002A0 nativeSetupParent002Xi0 := by rfl
  have hl : (nativeSetupParent002Ops.drop 132).length=341 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent002Ops.take 132)).getD 0 (.const 0)=parentRowFlatRootExpr 2 true := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent002Ops.take 132) (nativeSetupParent002Ops.drop 132) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_flat_root_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent002FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent002Real] using hh

/-- Exact dirichlet root at parent height 2. -/
theorem parent_row_flat_root_dirichlet_002 :
    nativeSetupParent002FieldsR.getD 9 0=parentRowFlatRootValue 2 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent002A0 nativeSetupParent002Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent002A0 nativeSetupParent002Xi0 := by rfl
  have hl : (nativeSetupParent002Ops.drop 133).length=340 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent002Ops.take 133)).getD 0 (.const 0)=parentRowFlatRootExpr 2 false := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent002Ops.take 133) (nativeSetupParent002Ops.drop 133) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_flat_root_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent002FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent002Real] using hh

/-- Exact joint root at parent height 3. -/
theorem parent_row_flat_root_joint_003 :
    nativeSetupParent003FieldsR.getD 8 0=parentRowFlatRootValue 3 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent003A0 nativeSetupParent003Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent003A0 nativeSetupParent003Xi0 := by rfl
  have hl : (nativeSetupParent003Ops.drop 163).length=338 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent003Ops.take 163)).getD 0 (.const 0)=parentRowFlatRootExpr 3 true := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent003Ops.take 163) (nativeSetupParent003Ops.drop 163) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_flat_root_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent003FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent003Real] using hh

/-- Exact dirichlet root at parent height 3. -/
theorem parent_row_flat_root_dirichlet_003 :
    nativeSetupParent003FieldsR.getD 9 0=parentRowFlatRootValue 3 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent003A0 nativeSetupParent003Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent003A0 nativeSetupParent003Xi0 := by rfl
  have hl : (nativeSetupParent003Ops.drop 164).length=337 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent003Ops.take 164)).getD 0 (.const 0)=parentRowFlatRootExpr 3 false := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent003Ops.take 164) (nativeSetupParent003Ops.drop 164) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_flat_root_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent003FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent003Real] using hh

/-- Exact joint root at parent height 4. -/
theorem parent_row_flat_root_joint_004 :
    nativeSetupParent004FieldsR.getD 8 0=parentRowFlatRootValue 4 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent004A0 nativeSetupParent004Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent004A0 nativeSetupParent004Xi0 := by rfl
  have hl : (nativeSetupParent004Ops.drop 194).length=335 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent004Ops.take 194)).getD 0 (.const 0)=parentRowFlatRootExpr 4 true := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent004Ops.take 194) (nativeSetupParent004Ops.drop 194) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_flat_root_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent004FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent004Real] using hh

/-- Exact dirichlet root at parent height 4. -/
theorem parent_row_flat_root_dirichlet_004 :
    nativeSetupParent004FieldsR.getD 9 0=parentRowFlatRootValue 4 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent004A0 nativeSetupParent004Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent004A0 nativeSetupParent004Xi0 := by rfl
  have hl : (nativeSetupParent004Ops.drop 195).length=334 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent004Ops.take 195)).getD 0 (.const 0)=parentRowFlatRootExpr 4 false := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent004Ops.take 195) (nativeSetupParent004Ops.drop 195) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_flat_root_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent004FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent004Real] using hh

/-- Exact joint root at parent height 5. -/
theorem parent_row_flat_root_joint_005 :
    nativeSetupParent005FieldsR.getD 8 0=parentRowFlatRootValue 5 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent005A0 nativeSetupParent005Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent005A0 nativeSetupParent005Xi0 := by rfl
  have hl : (nativeSetupParent005Ops.drop 225).length=332 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent005Ops.take 225)).getD 0 (.const 0)=parentRowFlatRootExpr 5 true := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent005Ops.take 225) (nativeSetupParent005Ops.drop 225) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_flat_root_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent005FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent005Real] using hh

/-- Exact dirichlet root at parent height 5. -/
theorem parent_row_flat_root_dirichlet_005 :
    nativeSetupParent005FieldsR.getD 9 0=parentRowFlatRootValue 5 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent005A0 nativeSetupParent005Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent005A0 nativeSetupParent005Xi0 := by rfl
  have hl : (nativeSetupParent005Ops.drop 226).length=331 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent005Ops.take 226)).getD 0 (.const 0)=parentRowFlatRootExpr 5 false := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent005Ops.take 226) (nativeSetupParent005Ops.drop 226) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_flat_root_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent005FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent005Real] using hh

/-- Exact joint root at parent height 6. -/
theorem parent_row_flat_root_joint_006 :
    nativeSetupParent006FieldsR.getD 8 0=parentRowFlatRootValue 6 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent006A0 nativeSetupParent006Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent006A0 nativeSetupParent006Xi0 := by rfl
  have hl : (nativeSetupParent006Ops.drop 256).length=332 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent006Ops.take 256)).getD 0 (.const 0)=parentRowFlatRootExpr 6 true := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent006Ops.take 256) (nativeSetupParent006Ops.drop 256) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_flat_root_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent006FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent006Real] using hh

/-- Exact dirichlet root at parent height 6. -/
theorem parent_row_flat_root_dirichlet_006 :
    nativeSetupParent006FieldsR.getD 9 0=parentRowFlatRootValue 6 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent006A0 nativeSetupParent006Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent006A0 nativeSetupParent006Xi0 := by rfl
  have hl : (nativeSetupParent006Ops.drop 257).length=331 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent006Ops.take 257)).getD 0 (.const 0)=parentRowFlatRootExpr 6 false := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent006Ops.take 257) (nativeSetupParent006Ops.drop 257) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_flat_root_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent006FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent006Real] using hh

/-- Exact joint root at parent height 7. -/
theorem parent_row_flat_root_joint_007 :
    nativeSetupParent007FieldsR.getD 8 0=parentRowFlatRootValue 7 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent007A0 nativeSetupParent007Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent007A0 nativeSetupParent007Xi0 := by rfl
  have hl : (nativeSetupParent007Ops.drop 286).length=332 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent007Ops.take 286)).getD 0 (.const 0)=parentRowFlatRootExpr 7 true := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent007Ops.take 286) (nativeSetupParent007Ops.drop 286) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_flat_root_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent007FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent007Real] using hh

/-- Exact dirichlet root at parent height 7. -/
theorem parent_row_flat_root_dirichlet_007 :
    nativeSetupParent007FieldsR.getD 9 0=parentRowFlatRootValue 7 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent007A0 nativeSetupParent007Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent007A0 nativeSetupParent007Xi0 := by rfl
  have hl : (nativeSetupParent007Ops.drop 287).length=331 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent007Ops.take 287)).getD 0 (.const 0)=parentRowFlatRootExpr 7 false := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent007Ops.take 287) (nativeSetupParent007Ops.drop 287) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_flat_root_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent007FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent007Real] using hh

/-- Exact joint root at parent height 8. -/
theorem parent_row_flat_root_joint_008 :
    nativeSetupParent008FieldsR.getD 8 0=parentRowFlatRootValue 8 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent008A0 nativeSetupParent008Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent008A0 nativeSetupParent008Xi0 := by rfl
  have hl : (nativeSetupParent008Ops.drop 317).length=332 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent008Ops.take 317)).getD 0 (.const 0)=parentRowFlatRootExpr 8 true := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent008Ops.take 317) (nativeSetupParent008Ops.drop 317) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_flat_root_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent008FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent008Real] using hh

/-- Exact dirichlet root at parent height 8. -/
theorem parent_row_flat_root_dirichlet_008 :
    nativeSetupParent008FieldsR.getD 9 0=parentRowFlatRootValue 8 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent008A0 nativeSetupParent008Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent008A0 nativeSetupParent008Xi0 := by rfl
  have hl : (nativeSetupParent008Ops.drop 318).length=331 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent008Ops.take 318)).getD 0 (.const 0)=parentRowFlatRootExpr 8 false := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent008Ops.take 318) (nativeSetupParent008Ops.drop 318) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_flat_root_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent008FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent008Real] using hh

/-- Exact joint root at parent height 9. -/
theorem parent_row_flat_root_joint_009 :
    nativeSetupParent009FieldsR.getD 8 0=parentRowFlatRootValue 9 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent009A0 nativeSetupParent009Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent009A0 nativeSetupParent009Xi0 := by rfl
  have hl : (nativeSetupParent009Ops.drop 347).length=332 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent009Ops.take 347)).getD 0 (.const 0)=parentRowFlatRootExpr 9 true := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent009Ops.take 347) (nativeSetupParent009Ops.drop 347) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_flat_root_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent009FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent009Real] using hh

/-- Exact dirichlet root at parent height 9. -/
theorem parent_row_flat_root_dirichlet_009 :
    nativeSetupParent009FieldsR.getD 9 0=parentRowFlatRootValue 9 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent009A0 nativeSetupParent009Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent009A0 nativeSetupParent009Xi0 := by rfl
  have hl : (nativeSetupParent009Ops.drop 348).length=331 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent009Ops.take 348)).getD 0 (.const 0)=parentRowFlatRootExpr 9 false := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent009Ops.take 348) (nativeSetupParent009Ops.drop 348) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_flat_root_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent009FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent009Real] using hh

/-- Exact joint root at parent height 10. -/
theorem parent_row_flat_root_joint_010 :
    nativeSetupParent010FieldsR.getD 8 0=parentRowFlatRootValue 10 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent010A0 nativeSetupParent010Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent010A0 nativeSetupParent010Xi0 := by rfl
  have hl : (nativeSetupParent010Ops.drop 378).length=332 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent010Ops.take 378)).getD 0 (.const 0)=parentRowFlatRootExpr 10 true := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent010Ops.take 378) (nativeSetupParent010Ops.drop 378) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_flat_root_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent010FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent010Real] using hh

/-- Exact dirichlet root at parent height 10. -/
theorem parent_row_flat_root_dirichlet_010 :
    nativeSetupParent010FieldsR.getD 9 0=parentRowFlatRootValue 10 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent010A0 nativeSetupParent010Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent010A0 nativeSetupParent010Xi0 := by rfl
  have hl : (nativeSetupParent010Ops.drop 379).length=331 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent010Ops.take 379)).getD 0 (.const 0)=parentRowFlatRootExpr 10 false := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent010Ops.take 379) (nativeSetupParent010Ops.drop 379) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_flat_root_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent010FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent010Real] using hh

/-- Exact joint root at parent height 11. -/
theorem parent_row_flat_root_joint_011 :
    nativeSetupParent011FieldsR.getD 8 0=parentRowFlatRootValue 11 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent011A0 nativeSetupParent011Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent011A0 nativeSetupParent011Xi0 := by rfl
  have hl : (nativeSetupParent011Ops.drop 408).length=332 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent011Ops.take 408)).getD 0 (.const 0)=parentRowFlatRootExpr 11 true := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent011Ops.take 408) (nativeSetupParent011Ops.drop 408) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_flat_root_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent011FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent011Real] using hh

/-- Exact dirichlet root at parent height 11. -/
theorem parent_row_flat_root_dirichlet_011 :
    nativeSetupParent011FieldsR.getD 9 0=parentRowFlatRootValue 11 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent011A0 nativeSetupParent011Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent011A0 nativeSetupParent011Xi0 := by rfl
  have hl : (nativeSetupParent011Ops.drop 409).length=331 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent011Ops.take 409)).getD 0 (.const 0)=parentRowFlatRootExpr 11 false := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent011Ops.take 409) (nativeSetupParent011Ops.drop 409) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_flat_root_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent011FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent011Real] using hh

/-- Exact joint root at parent height 12. -/
theorem parent_row_flat_root_joint_012 :
    nativeSetupParent012FieldsR.getD 8 0=parentRowFlatRootValue 12 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent012A0 nativeSetupParent012Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent012A0 nativeSetupParent012Xi0 := by rfl
  have hl : (nativeSetupParent012Ops.drop 439).length=332 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent012Ops.take 439)).getD 0 (.const 0)=parentRowFlatRootExpr 12 true := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent012Ops.take 439) (nativeSetupParent012Ops.drop 439) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_flat_root_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent012FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent012Real] using hh

/-- Exact dirichlet root at parent height 12. -/
theorem parent_row_flat_root_dirichlet_012 :
    nativeSetupParent012FieldsR.getD 9 0=parentRowFlatRootValue 12 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent012A0 nativeSetupParent012Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent012A0 nativeSetupParent012Xi0 := by rfl
  have hl : (nativeSetupParent012Ops.drop 440).length=331 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent012Ops.take 440)).getD 0 (.const 0)=parentRowFlatRootExpr 12 false := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent012Ops.take 440) (nativeSetupParent012Ops.drop 440) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_flat_root_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent012FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent012Real] using hh

/-- Exact joint root at parent height 13. -/
theorem parent_row_flat_root_joint_013 :
    nativeSetupParent013FieldsR.getD 8 0=parentRowFlatRootValue 13 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent013A0 nativeSetupParent013Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent013A0 nativeSetupParent013Xi0 := by rfl
  have hl : (nativeSetupParent013Ops.drop 469).length=332 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent013Ops.take 469)).getD 0 (.const 0)=parentRowFlatRootExpr 13 true := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent013Ops.take 469) (nativeSetupParent013Ops.drop 469) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_flat_root_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent013FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent013Real] using hh

/-- Exact dirichlet root at parent height 13. -/
theorem parent_row_flat_root_dirichlet_013 :
    nativeSetupParent013FieldsR.getD 9 0=parentRowFlatRootValue 13 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent013A0 nativeSetupParent013Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent013A0 nativeSetupParent013Xi0 := by rfl
  have hl : (nativeSetupParent013Ops.drop 470).length=331 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent013Ops.take 470)).getD 0 (.const 0)=parentRowFlatRootExpr 13 false := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent013Ops.take 470) (nativeSetupParent013Ops.drop 470) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_flat_root_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent013FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent013Real] using hh

/-- Exact joint root at parent height 14. -/
theorem parent_row_flat_root_joint_014 :
    nativeSetupParent014FieldsR.getD 8 0=parentRowFlatRootValue 14 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent014A0 nativeSetupParent014Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent014A0 nativeSetupParent014Xi0 := by rfl
  have hl : (nativeSetupParent014Ops.drop 500).length=332 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent014Ops.take 500)).getD 0 (.const 0)=parentRowFlatRootExpr 14 true := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent014Ops.take 500) (nativeSetupParent014Ops.drop 500) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_flat_root_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent014FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent014Real] using hh

/-- Exact dirichlet root at parent height 14. -/
theorem parent_row_flat_root_dirichlet_014 :
    nativeSetupParent014FieldsR.getD 9 0=parentRowFlatRootValue 14 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent014A0 nativeSetupParent014Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent014A0 nativeSetupParent014Xi0 := by rfl
  have hl : (nativeSetupParent014Ops.drop 501).length=331 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent014Ops.take 501)).getD 0 (.const 0)=parentRowFlatRootExpr 14 false := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent014Ops.take 501) (nativeSetupParent014Ops.drop 501) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_flat_root_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent014FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent014Real] using hh

/-- Exact joint root at parent height 15. -/
theorem parent_row_flat_root_joint_015 :
    nativeSetupParent015FieldsR.getD 8 0=parentRowFlatRootValue 15 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent015A0 nativeSetupParent015Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent015A0 nativeSetupParent015Xi0 := by rfl
  have hl : (nativeSetupParent015Ops.drop 530).length=332 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent015Ops.take 530)).getD 0 (.const 0)=parentRowFlatRootExpr 15 true := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent015Ops.take 530) (nativeSetupParent015Ops.drop 530) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_flat_root_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent015FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent015Real] using hh

/-- Exact dirichlet root at parent height 15. -/
theorem parent_row_flat_root_dirichlet_015 :
    nativeSetupParent015FieldsR.getD 9 0=parentRowFlatRootValue 15 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent015A0 nativeSetupParent015Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent015A0 nativeSetupParent015Xi0 := by rfl
  have hl : (nativeSetupParent015Ops.drop 531).length=331 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent015Ops.take 531)).getD 0 (.const 0)=parentRowFlatRootExpr 15 false := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent015Ops.take 531) (nativeSetupParent015Ops.drop 531) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_flat_root_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent015FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent015Real] using hh

/-- Exact joint root at parent height 16. -/
theorem parent_row_flat_root_joint_016 :
    nativeSetupParent016FieldsR.getD 8 0=parentRowFlatRootValue 16 true := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent016A0 nativeSetupParent016Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent016A0 nativeSetupParent016Xi0 := by rfl
  have hl : (nativeSetupParent016Ops.drop 561).length=332 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent016Ops.take 561)).getD 0 (.const 0)=parentRowFlatRootExpr 16 true := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent016Ops.take 561) (nativeSetupParent016Ops.drop 561) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_flat_root_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent016FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent016Real] using hh

/-- Exact dirichlet root at parent height 16. -/
theorem parent_row_flat_root_dirichlet_016 :
    nativeSetupParent016FieldsR.getD 9 0=parentRowFlatRootValue 16 false := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent016A0 nativeSetupParent016Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent016A0 nativeSetupParent016Xi0 := by rfl
  have hl : (nativeSetupParent016Ops.drop 562).length=331 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent016Ops.take 562)).getD 0 (.const 0)=parentRowFlatRootExpr 16 false := by
    decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent016Ops.take 562) (nativeSetupParent016Ops.drop 562) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he,parent_row_flat_root_expr_eval env (by rfl)] at hh
  simpa only [nativeSetupParent016FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent016Real] using hh

/-- Both aggregate root fields retain their exact finite-band meaning. -/
theorem parent_row_flat_root_field (j : Fin 16) (joint : Bool) :
    (parentRowFields j).getD (if joint then 8 else 9) 0=
      parentRowFlatRootValue (j.val+1) joint := by
  cases joint
  · fin_cases j <;> simp only [Bool.false_eq_true,ite_false,parentRowFields,
      nativeConfiguredParentEndpoint,nativeParentEndpointCertificates,nativeParent001EndpointCertificate,nativeParent002EndpointCertificate,nativeParent003EndpointCertificate,nativeParent004EndpointCertificate,nativeParent005EndpointCertificate,nativeParent006EndpointCertificate,nativeParent007EndpointCertificate,nativeParent008EndpointCertificate,nativeParent009EndpointCertificate,nativeParent010EndpointCertificate,nativeParent011EndpointCertificate,nativeParent012EndpointCertificate,nativeParent013EndpointCertificate,nativeParent014EndpointCertificate,nativeParent015EndpointCertificate,nativeParent016EndpointCertificate,
      List.getD_cons_zero,List.getD_cons_succ]
    · exact parent_row_flat_root_dirichlet_001
    · exact parent_row_flat_root_dirichlet_002
    · exact parent_row_flat_root_dirichlet_003
    · exact parent_row_flat_root_dirichlet_004
    · exact parent_row_flat_root_dirichlet_005
    · exact parent_row_flat_root_dirichlet_006
    · exact parent_row_flat_root_dirichlet_007
    · exact parent_row_flat_root_dirichlet_008
    · exact parent_row_flat_root_dirichlet_009
    · exact parent_row_flat_root_dirichlet_010
    · exact parent_row_flat_root_dirichlet_011
    · exact parent_row_flat_root_dirichlet_012
    · exact parent_row_flat_root_dirichlet_013
    · exact parent_row_flat_root_dirichlet_014
    · exact parent_row_flat_root_dirichlet_015
    · exact parent_row_flat_root_dirichlet_016
  · fin_cases j <;> simp only [ite_true,parentRowFields,
      nativeConfiguredParentEndpoint,nativeParentEndpointCertificates,nativeParent001EndpointCertificate,nativeParent002EndpointCertificate,nativeParent003EndpointCertificate,nativeParent004EndpointCertificate,nativeParent005EndpointCertificate,nativeParent006EndpointCertificate,nativeParent007EndpointCertificate,nativeParent008EndpointCertificate,nativeParent009EndpointCertificate,nativeParent010EndpointCertificate,nativeParent011EndpointCertificate,nativeParent012EndpointCertificate,nativeParent013EndpointCertificate,nativeParent014EndpointCertificate,nativeParent015EndpointCertificate,nativeParent016EndpointCertificate,
      List.getD_cons_zero,List.getD_cons_succ]
    · exact parent_row_flat_root_joint_001
    · exact parent_row_flat_root_joint_002
    · exact parent_row_flat_root_joint_003
    · exact parent_row_flat_root_joint_004
    · exact parent_row_flat_root_joint_005
    · exact parent_row_flat_root_joint_006
    · exact parent_row_flat_root_joint_007
    · exact parent_row_flat_root_joint_008
    · exact parent_row_flat_root_joint_009
    · exact parent_row_flat_root_joint_010
    · exact parent_row_flat_root_joint_011
    · exact parent_row_flat_root_joint_012
    · exact parent_row_flat_root_joint_013
    · exact parent_row_flat_root_joint_014
    · exact parent_row_flat_root_joint_015
    · exact parent_row_flat_root_joint_016

end
end ASDExplicitGamma.Native
