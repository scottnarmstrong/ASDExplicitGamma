module

public import ASDExplicitGamma.Native.ParentRowSymbolic
public import ASDExplicitGamma.Native.ParentRowCertificates

/-! Exact initial history field in every parent source program. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native Numerics.Mirror
noncomputable section

/-- Initial history at parent depth 1 is the exact mesh-five value. -/
theorem parent_row_h0_001 :
    nativeSetupParent001FieldsR.getD 13 0=(3:ℝ)^((3:ℝ)/4) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent001A0 nativeSetupParent001Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent001A0 nativeSetupParent001Xi0 := by rfl
  have hl : (nativeSetupParent001Ops.drop 19).length=426 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent001Ops.take 19)).getD 0 (.const 0)=
      .exp (.mul (.var 2) (.const (3/4))) := by decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent001Ops.take 19) (nativeSetupParent001Ops.drop 19) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent001FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent001Real]
  rw [hh]
  change Real.exp (Real.log 3*((3/4:ℚ):ℝ))=_
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3)]
  norm_num

/-- Initial history at parent depth 2 is the exact mesh-five value. -/
theorem parent_row_h0_002 :
    nativeSetupParent002FieldsR.getD 13 0=(3:ℝ)^((3:ℝ)/4) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent002A0 nativeSetupParent002Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent002A0 nativeSetupParent002Xi0 := by rfl
  have hl : (nativeSetupParent002Ops.drop 19).length=454 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent002Ops.take 19)).getD 0 (.const 0)=
      .exp (.mul (.var 2) (.const (3/4))) := by decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent002Ops.take 19) (nativeSetupParent002Ops.drop 19) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent002FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent002Real]
  rw [hh]
  change Real.exp (Real.log 3*((3/4:ℚ):ℝ))=_
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3)]
  norm_num

/-- Initial history at parent depth 3 is the exact mesh-five value. -/
theorem parent_row_h0_003 :
    nativeSetupParent003FieldsR.getD 13 0=(3:ℝ)^((3:ℝ)/4) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent003A0 nativeSetupParent003Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent003A0 nativeSetupParent003Xi0 := by rfl
  have hl : (nativeSetupParent003Ops.drop 19).length=482 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent003Ops.take 19)).getD 0 (.const 0)=
      .exp (.mul (.var 2) (.const (3/4))) := by decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent003Ops.take 19) (nativeSetupParent003Ops.drop 19) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent003FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent003Real]
  rw [hh]
  change Real.exp (Real.log 3*((3/4:ℚ):ℝ))=_
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3)]
  norm_num

/-- Initial history at parent depth 4 is the exact mesh-five value. -/
theorem parent_row_h0_004 :
    nativeSetupParent004FieldsR.getD 13 0=(3:ℝ)^((3:ℝ)/4) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent004A0 nativeSetupParent004Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent004A0 nativeSetupParent004Xi0 := by rfl
  have hl : (nativeSetupParent004Ops.drop 19).length=510 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent004Ops.take 19)).getD 0 (.const 0)=
      .exp (.mul (.var 2) (.const (3/4))) := by decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent004Ops.take 19) (nativeSetupParent004Ops.drop 19) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent004FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent004Real]
  rw [hh]
  change Real.exp (Real.log 3*((3/4:ℚ):ℝ))=_
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3)]
  norm_num

/-- Initial history at parent depth 5 is the exact mesh-five value. -/
theorem parent_row_h0_005 :
    nativeSetupParent005FieldsR.getD 13 0=(3:ℝ)^((3:ℝ)/4) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent005A0 nativeSetupParent005Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent005A0 nativeSetupParent005Xi0 := by rfl
  have hl : (nativeSetupParent005Ops.drop 19).length=538 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent005Ops.take 19)).getD 0 (.const 0)=
      .exp (.mul (.var 2) (.const (3/4))) := by decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent005Ops.take 19) (nativeSetupParent005Ops.drop 19) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent005FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent005Real]
  rw [hh]
  change Real.exp (Real.log 3*((3/4:ℚ):ℝ))=_
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3)]
  norm_num

/-- Initial history at parent depth 6 is the exact mesh-five value. -/
theorem parent_row_h0_006 :
    nativeSetupParent006FieldsR.getD 13 0=(3:ℝ)^((3:ℝ)/4) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent006A0 nativeSetupParent006Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent006A0 nativeSetupParent006Xi0 := by rfl
  have hl : (nativeSetupParent006Ops.drop 19).length=569 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent006Ops.take 19)).getD 0 (.const 0)=
      .exp (.mul (.var 2) (.const (3/4))) := by decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent006Ops.take 19) (nativeSetupParent006Ops.drop 19) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent006FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent006Real]
  rw [hh]
  change Real.exp (Real.log 3*((3/4:ℚ):ℝ))=_
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3)]
  norm_num

/-- Initial history at parent depth 7 is the exact mesh-five value. -/
theorem parent_row_h0_007 :
    nativeSetupParent007FieldsR.getD 13 0=(3:ℝ)^((3:ℝ)/4) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent007A0 nativeSetupParent007Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent007A0 nativeSetupParent007Xi0 := by rfl
  have hl : (nativeSetupParent007Ops.drop 19).length=599 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent007Ops.take 19)).getD 0 (.const 0)=
      .exp (.mul (.var 2) (.const (3/4))) := by decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent007Ops.take 19) (nativeSetupParent007Ops.drop 19) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent007FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent007Real]
  rw [hh]
  change Real.exp (Real.log 3*((3/4:ℚ):ℝ))=_
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3)]
  norm_num

/-- Initial history at parent depth 8 is the exact mesh-five value. -/
theorem parent_row_h0_008 :
    nativeSetupParent008FieldsR.getD 13 0=(3:ℝ)^((3:ℝ)/4) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent008A0 nativeSetupParent008Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent008A0 nativeSetupParent008Xi0 := by rfl
  have hl : (nativeSetupParent008Ops.drop 19).length=630 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent008Ops.take 19)).getD 0 (.const 0)=
      .exp (.mul (.var 2) (.const (3/4))) := by decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent008Ops.take 19) (nativeSetupParent008Ops.drop 19) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent008FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent008Real]
  rw [hh]
  change Real.exp (Real.log 3*((3/4:ℚ):ℝ))=_
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3)]
  norm_num

/-- Initial history at parent depth 9 is the exact mesh-five value. -/
theorem parent_row_h0_009 :
    nativeSetupParent009FieldsR.getD 13 0=(3:ℝ)^((3:ℝ)/4) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent009A0 nativeSetupParent009Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent009A0 nativeSetupParent009Xi0 := by rfl
  have hl : (nativeSetupParent009Ops.drop 19).length=660 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent009Ops.take 19)).getD 0 (.const 0)=
      .exp (.mul (.var 2) (.const (3/4))) := by decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent009Ops.take 19) (nativeSetupParent009Ops.drop 19) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent009FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent009Real]
  rw [hh]
  change Real.exp (Real.log 3*((3/4:ℚ):ℝ))=_
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3)]
  norm_num

/-- Initial history at parent depth 10 is the exact mesh-five value. -/
theorem parent_row_h0_010 :
    nativeSetupParent010FieldsR.getD 13 0=(3:ℝ)^((3:ℝ)/4) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent010A0 nativeSetupParent010Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent010A0 nativeSetupParent010Xi0 := by rfl
  have hl : (nativeSetupParent010Ops.drop 19).length=691 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent010Ops.take 19)).getD 0 (.const 0)=
      .exp (.mul (.var 2) (.const (3/4))) := by decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent010Ops.take 19) (nativeSetupParent010Ops.drop 19) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent010FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent010Real]
  rw [hh]
  change Real.exp (Real.log 3*((3/4:ℚ):ℝ))=_
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3)]
  norm_num

/-- Initial history at parent depth 11 is the exact mesh-five value. -/
theorem parent_row_h0_011 :
    nativeSetupParent011FieldsR.getD 13 0=(3:ℝ)^((3:ℝ)/4) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent011A0 nativeSetupParent011Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent011A0 nativeSetupParent011Xi0 := by rfl
  have hl : (nativeSetupParent011Ops.drop 19).length=721 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent011Ops.take 19)).getD 0 (.const 0)=
      .exp (.mul (.var 2) (.const (3/4))) := by decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent011Ops.take 19) (nativeSetupParent011Ops.drop 19) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent011FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent011Real]
  rw [hh]
  change Real.exp (Real.log 3*((3/4:ℚ):ℝ))=_
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3)]
  norm_num

/-- Initial history at parent depth 12 is the exact mesh-five value. -/
theorem parent_row_h0_012 :
    nativeSetupParent012FieldsR.getD 13 0=(3:ℝ)^((3:ℝ)/4) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent012A0 nativeSetupParent012Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent012A0 nativeSetupParent012Xi0 := by rfl
  have hl : (nativeSetupParent012Ops.drop 19).length=752 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent012Ops.take 19)).getD 0 (.const 0)=
      .exp (.mul (.var 2) (.const (3/4))) := by decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent012Ops.take 19) (nativeSetupParent012Ops.drop 19) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent012FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent012Real]
  rw [hh]
  change Real.exp (Real.log 3*((3/4:ℚ):ℝ))=_
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3)]
  norm_num

/-- Initial history at parent depth 13 is the exact mesh-five value. -/
theorem parent_row_h0_013 :
    nativeSetupParent013FieldsR.getD 13 0=(3:ℝ)^((3:ℝ)/4) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent013A0 nativeSetupParent013Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent013A0 nativeSetupParent013Xi0 := by rfl
  have hl : (nativeSetupParent013Ops.drop 19).length=782 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent013Ops.take 19)).getD 0 (.const 0)=
      .exp (.mul (.var 2) (.const (3/4))) := by decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent013Ops.take 19) (nativeSetupParent013Ops.drop 19) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent013FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent013Real]
  rw [hh]
  change Real.exp (Real.log 3*((3/4:ℚ):ℝ))=_
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3)]
  norm_num

/-- Initial history at parent depth 14 is the exact mesh-five value. -/
theorem parent_row_h0_014 :
    nativeSetupParent014FieldsR.getD 13 0=(3:ℝ)^((3:ℝ)/4) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent014A0 nativeSetupParent014Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent014A0 nativeSetupParent014Xi0 := by rfl
  have hl : (nativeSetupParent014Ops.drop 19).length=813 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent014Ops.take 19)).getD 0 (.const 0)=
      .exp (.mul (.var 2) (.const (3/4))) := by decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent014Ops.take 19) (nativeSetupParent014Ops.drop 19) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent014FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent014Real]
  rw [hh]
  change Real.exp (Real.log 3*((3/4:ℚ):ℝ))=_
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3)]
  norm_num

/-- Initial history at parent depth 15 is the exact mesh-five value. -/
theorem parent_row_h0_015 :
    nativeSetupParent015FieldsR.getD 13 0=(3:ℝ)^((3:ℝ)/4) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent015A0 nativeSetupParent015Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent015A0 nativeSetupParent015Xi0 := by rfl
  have hl : (nativeSetupParent015Ops.drop 19).length=843 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent015Ops.take 19)).getD 0 (.const 0)=
      .exp (.mul (.var 2) (.const (3/4))) := by decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent015Ops.take 19) (nativeSetupParent015Ops.drop 19) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent015FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent015Real]
  rw [hh]
  change Real.exp (Real.log 3*((3/4:ℚ):ℝ))=_
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3)]
  norm_num

/-- Initial history at parent depth 16 is the exact mesh-five value. -/
theorem parent_row_h0_016 :
    nativeSetupParent016FieldsR.getD 13 0=(3:ℝ)^((3:ℝ)/4) := by
  let env := fun i => (nativeSetupInputReal nativeSetupParent016A0 nativeSetupParent016Xi0).getD i 0
  have hin : ([Expr.var 0,.var 1,.var 2].map (evalReal env))=
      nativeSetupInputReal nativeSetupParent016A0 nativeSetupParent016Xi0 := by rfl
  have hl : (nativeSetupParent016Ops.drop 19).length=874 := by decide +kernel
  have he : (parentRowExprPlan [.var 0,.var 1,.var 2]
      (nativeSetupParent016Ops.take 19)).getD 0 (.const 0)=
      .exp (.mul (.var 2) (.const (3/4))) := by decide +kernel
  have hh := parent_row_symbolic_entry env [.var 0,.var 1,.var 2]
    (nativeSetupParent016Ops.take 19) (nativeSetupParent016Ops.drop 19) 0
  rw [hin,List.take_append_drop,hl,Nat.add_zero,he] at hh
  simp only [nativeSetupParent016FieldsR,List.getD_cons_zero,List.getD_cons_succ,nativeSetupParent016Real]
  rw [hh]
  change Real.exp (Real.log 3*((3/4:ℚ):ℝ))=_
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3)]
  norm_num

/-- Every selected panel retains the exact mesh-five initial history. -/
theorem parent_row_h0_field (j : Fin 16) :
    (parentRowFields j).getD 13 0=(3:ℝ)^((3:ℝ)/4) := by
  fin_cases j <;> simp only [parentRowFields,nativeConfiguredParentEndpoint,
    nativeParentEndpointCertificates,nativeParent001EndpointCertificate, nativeParent002EndpointCertificate, nativeParent003EndpointCertificate, nativeParent004EndpointCertificate, nativeParent005EndpointCertificate, nativeParent006EndpointCertificate, nativeParent007EndpointCertificate, nativeParent008EndpointCertificate, nativeParent009EndpointCertificate, nativeParent010EndpointCertificate, nativeParent011EndpointCertificate, nativeParent012EndpointCertificate, nativeParent013EndpointCertificate, nativeParent014EndpointCertificate, nativeParent015EndpointCertificate, nativeParent016EndpointCertificate,List.getD_cons_zero,List.getD_cons_succ]
  · exact parent_row_h0_001
  · exact parent_row_h0_002
  · exact parent_row_h0_003
  · exact parent_row_h0_004
  · exact parent_row_h0_005
  · exact parent_row_h0_006
  · exact parent_row_h0_007
  · exact parent_row_h0_008
  · exact parent_row_h0_009
  · exact parent_row_h0_010
  · exact parent_row_h0_011
  · exact parent_row_h0_012
  · exact parent_row_h0_013
  · exact parent_row_h0_014
  · exact parent_row_h0_015
  · exact parent_row_h0_016

end
end ASDExplicitGamma.Native
