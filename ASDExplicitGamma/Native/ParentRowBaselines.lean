module

public import ASDExplicitGamma.Native.ParentRowCertificates
public import ASDExplicitGamma.Native.ParentRowProgram

/-! The parent source programs retain twice the full band variance as baseline.
The signed inverse return is accounted for separately. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native Numerics.Mirror
noncomputable section

/-- The depth-1 flat baseline is exactly twice the stored full variance. -/
theorem parent_row_baseline_001 :
    nativeSetupParent001B0R=2*nativeSetupParent001FieldsR.getD 0 0 := by
  have hs : nativeSetupParent001Ops=nativeSetupParent001Ops.take 65++
      (.mul (.var 39) (.var 64)::nativeSetupParent001Ops.drop 66) := by decide +kernel
  have hl : (nativeSetupParent001Ops.drop 66).length=379 := by decide +kernel
  have hm := parent_row_program_mul (nativeSetupInputReal nativeSetupParent001A0 nativeSetupParent001Xi0)
    (nativeSetupParent001Ops.take 65) (nativeSetupParent001Ops.drop 66) 39 64
  dsimp only at hm
  rw [←hs,hl] at hm
  have hf : nativeSetupParent001Ops=.const 2::nativeSetupParent001Ops.drop 1 := by decide +kernel
  have hfl : (nativeSetupParent001Ops.drop 1).length=444 := by decide +kernel
  have hc := parent_row_program_first_constant
    (nativeSetupInputReal nativeSetupParent001A0 nativeSetupParent001Xi0) 2 (nativeSetupParent001Ops.drop 1)
  rw [←hf,hfl] at hc
  simp only [nativeSetupParent001B0R,nativeSetupParent001FieldsR,List.getD_cons_zero,nativeSetupParent001Real]
  rw [hm]
  norm_num only [Nat.reduceAdd] at hc ⊢
  rw [hc]
  ring

/-- The depth-2 flat baseline is exactly twice the stored full variance. -/
theorem parent_row_baseline_002 :
    nativeSetupParent002B0R=2*nativeSetupParent002FieldsR.getD 0 0 := by
  have hs : nativeSetupParent002Ops=nativeSetupParent002Ops.take 76++
      (.mul (.var 45) (.var 75)::nativeSetupParent002Ops.drop 77) := by decide +kernel
  have hl : (nativeSetupParent002Ops.drop 77).length=396 := by decide +kernel
  have hm := parent_row_program_mul (nativeSetupInputReal nativeSetupParent002A0 nativeSetupParent002Xi0)
    (nativeSetupParent002Ops.take 76) (nativeSetupParent002Ops.drop 77) 45 75
  dsimp only at hm
  rw [←hs,hl] at hm
  have hf : nativeSetupParent002Ops=.const 2::nativeSetupParent002Ops.drop 1 := by decide +kernel
  have hfl : (nativeSetupParent002Ops.drop 1).length=472 := by decide +kernel
  have hc := parent_row_program_first_constant
    (nativeSetupInputReal nativeSetupParent002A0 nativeSetupParent002Xi0) 2 (nativeSetupParent002Ops.drop 1)
  rw [←hf,hfl] at hc
  simp only [nativeSetupParent002B0R,nativeSetupParent002FieldsR,List.getD_cons_zero,nativeSetupParent002Real]
  rw [hm]
  norm_num only [Nat.reduceAdd] at hc ⊢
  rw [hc]
  ring

/-- The depth-3 flat baseline is exactly twice the stored full variance. -/
theorem parent_row_baseline_003 :
    nativeSetupParent003B0R=2*nativeSetupParent003FieldsR.getD 0 0 := by
  have hs : nativeSetupParent003Ops=nativeSetupParent003Ops.take 87++
      (.mul (.var 51) (.var 86)::nativeSetupParent003Ops.drop 88) := by decide +kernel
  have hl : (nativeSetupParent003Ops.drop 88).length=413 := by decide +kernel
  have hm := parent_row_program_mul (nativeSetupInputReal nativeSetupParent003A0 nativeSetupParent003Xi0)
    (nativeSetupParent003Ops.take 87) (nativeSetupParent003Ops.drop 88) 51 86
  dsimp only at hm
  rw [←hs,hl] at hm
  have hf : nativeSetupParent003Ops=.const 2::nativeSetupParent003Ops.drop 1 := by decide +kernel
  have hfl : (nativeSetupParent003Ops.drop 1).length=500 := by decide +kernel
  have hc := parent_row_program_first_constant
    (nativeSetupInputReal nativeSetupParent003A0 nativeSetupParent003Xi0) 2 (nativeSetupParent003Ops.drop 1)
  rw [←hf,hfl] at hc
  simp only [nativeSetupParent003B0R,nativeSetupParent003FieldsR,List.getD_cons_zero,nativeSetupParent003Real]
  rw [hm]
  norm_num only [Nat.reduceAdd] at hc ⊢
  rw [hc]
  ring

/-- The depth-4 flat baseline is exactly twice the stored full variance. -/
theorem parent_row_baseline_004 :
    nativeSetupParent004B0R=2*nativeSetupParent004FieldsR.getD 0 0 := by
  have hs : nativeSetupParent004Ops=nativeSetupParent004Ops.take 98++
      (.mul (.var 57) (.var 97)::nativeSetupParent004Ops.drop 99) := by decide +kernel
  have hl : (nativeSetupParent004Ops.drop 99).length=430 := by decide +kernel
  have hm := parent_row_program_mul (nativeSetupInputReal nativeSetupParent004A0 nativeSetupParent004Xi0)
    (nativeSetupParent004Ops.take 98) (nativeSetupParent004Ops.drop 99) 57 97
  dsimp only at hm
  rw [←hs,hl] at hm
  have hf : nativeSetupParent004Ops=.const 2::nativeSetupParent004Ops.drop 1 := by decide +kernel
  have hfl : (nativeSetupParent004Ops.drop 1).length=528 := by decide +kernel
  have hc := parent_row_program_first_constant
    (nativeSetupInputReal nativeSetupParent004A0 nativeSetupParent004Xi0) 2 (nativeSetupParent004Ops.drop 1)
  rw [←hf,hfl] at hc
  simp only [nativeSetupParent004B0R,nativeSetupParent004FieldsR,List.getD_cons_zero,nativeSetupParent004Real]
  rw [hm]
  norm_num only [Nat.reduceAdd] at hc ⊢
  rw [hc]
  ring

/-- The depth-5 flat baseline is exactly twice the stored full variance. -/
theorem parent_row_baseline_005 :
    nativeSetupParent005B0R=2*nativeSetupParent005FieldsR.getD 0 0 := by
  have hs : nativeSetupParent005Ops=nativeSetupParent005Ops.take 109++
      (.mul (.var 63) (.var 108)::nativeSetupParent005Ops.drop 110) := by decide +kernel
  have hl : (nativeSetupParent005Ops.drop 110).length=447 := by decide +kernel
  have hm := parent_row_program_mul (nativeSetupInputReal nativeSetupParent005A0 nativeSetupParent005Xi0)
    (nativeSetupParent005Ops.take 109) (nativeSetupParent005Ops.drop 110) 63 108
  dsimp only at hm
  rw [←hs,hl] at hm
  have hf : nativeSetupParent005Ops=.const 2::nativeSetupParent005Ops.drop 1 := by decide +kernel
  have hfl : (nativeSetupParent005Ops.drop 1).length=556 := by decide +kernel
  have hc := parent_row_program_first_constant
    (nativeSetupInputReal nativeSetupParent005A0 nativeSetupParent005Xi0) 2 (nativeSetupParent005Ops.drop 1)
  rw [←hf,hfl] at hc
  simp only [nativeSetupParent005B0R,nativeSetupParent005FieldsR,List.getD_cons_zero,nativeSetupParent005Real]
  rw [hm]
  norm_num only [Nat.reduceAdd] at hc ⊢
  rw [hc]
  ring

/-- The depth-6 flat baseline is exactly twice the stored full variance. -/
theorem parent_row_baseline_006 :
    nativeSetupParent006B0R=2*nativeSetupParent006FieldsR.getD 0 0 := by
  have hs : nativeSetupParent006Ops=nativeSetupParent006Ops.take 120++
      (.mul (.var 69) (.var 119)::nativeSetupParent006Ops.drop 121) := by decide +kernel
  have hl : (nativeSetupParent006Ops.drop 121).length=467 := by decide +kernel
  have hm := parent_row_program_mul (nativeSetupInputReal nativeSetupParent006A0 nativeSetupParent006Xi0)
    (nativeSetupParent006Ops.take 120) (nativeSetupParent006Ops.drop 121) 69 119
  dsimp only at hm
  rw [←hs,hl] at hm
  have hf : nativeSetupParent006Ops=.const 2::nativeSetupParent006Ops.drop 1 := by decide +kernel
  have hfl : (nativeSetupParent006Ops.drop 1).length=587 := by decide +kernel
  have hc := parent_row_program_first_constant
    (nativeSetupInputReal nativeSetupParent006A0 nativeSetupParent006Xi0) 2 (nativeSetupParent006Ops.drop 1)
  rw [←hf,hfl] at hc
  simp only [nativeSetupParent006B0R,nativeSetupParent006FieldsR,List.getD_cons_zero,nativeSetupParent006Real]
  rw [hm]
  norm_num only [Nat.reduceAdd] at hc ⊢
  rw [hc]
  ring

/-- The depth-7 flat baseline is exactly twice the stored full variance. -/
theorem parent_row_baseline_007 :
    nativeSetupParent007B0R=2*nativeSetupParent007FieldsR.getD 0 0 := by
  have hs : nativeSetupParent007Ops=nativeSetupParent007Ops.take 130++
      (.mul (.var 74) (.var 129)::nativeSetupParent007Ops.drop 131) := by decide +kernel
  have hl : (nativeSetupParent007Ops.drop 131).length=487 := by decide +kernel
  have hm := parent_row_program_mul (nativeSetupInputReal nativeSetupParent007A0 nativeSetupParent007Xi0)
    (nativeSetupParent007Ops.take 130) (nativeSetupParent007Ops.drop 131) 74 129
  dsimp only at hm
  rw [←hs,hl] at hm
  have hf : nativeSetupParent007Ops=.const 2::nativeSetupParent007Ops.drop 1 := by decide +kernel
  have hfl : (nativeSetupParent007Ops.drop 1).length=617 := by decide +kernel
  have hc := parent_row_program_first_constant
    (nativeSetupInputReal nativeSetupParent007A0 nativeSetupParent007Xi0) 2 (nativeSetupParent007Ops.drop 1)
  rw [←hf,hfl] at hc
  simp only [nativeSetupParent007B0R,nativeSetupParent007FieldsR,List.getD_cons_zero,nativeSetupParent007Real]
  rw [hm]
  norm_num only [Nat.reduceAdd] at hc ⊢
  rw [hc]
  ring

/-- The depth-8 flat baseline is exactly twice the stored full variance. -/
theorem parent_row_baseline_008 :
    nativeSetupParent008B0R=2*nativeSetupParent008FieldsR.getD 0 0 := by
  have hs : nativeSetupParent008Ops=nativeSetupParent008Ops.take 141++
      (.mul (.var 80) (.var 140)::nativeSetupParent008Ops.drop 142) := by decide +kernel
  have hl : (nativeSetupParent008Ops.drop 142).length=507 := by decide +kernel
  have hm := parent_row_program_mul (nativeSetupInputReal nativeSetupParent008A0 nativeSetupParent008Xi0)
    (nativeSetupParent008Ops.take 141) (nativeSetupParent008Ops.drop 142) 80 140
  dsimp only at hm
  rw [←hs,hl] at hm
  have hf : nativeSetupParent008Ops=.const 2::nativeSetupParent008Ops.drop 1 := by decide +kernel
  have hfl : (nativeSetupParent008Ops.drop 1).length=648 := by decide +kernel
  have hc := parent_row_program_first_constant
    (nativeSetupInputReal nativeSetupParent008A0 nativeSetupParent008Xi0) 2 (nativeSetupParent008Ops.drop 1)
  rw [←hf,hfl] at hc
  simp only [nativeSetupParent008B0R,nativeSetupParent008FieldsR,List.getD_cons_zero,nativeSetupParent008Real]
  rw [hm]
  norm_num only [Nat.reduceAdd] at hc ⊢
  rw [hc]
  ring

/-- The depth-9 flat baseline is exactly twice the stored full variance. -/
theorem parent_row_baseline_009 :
    nativeSetupParent009B0R=2*nativeSetupParent009FieldsR.getD 0 0 := by
  have hs : nativeSetupParent009Ops=nativeSetupParent009Ops.take 151++
      (.mul (.var 85) (.var 150)::nativeSetupParent009Ops.drop 152) := by decide +kernel
  have hl : (nativeSetupParent009Ops.drop 152).length=527 := by decide +kernel
  have hm := parent_row_program_mul (nativeSetupInputReal nativeSetupParent009A0 nativeSetupParent009Xi0)
    (nativeSetupParent009Ops.take 151) (nativeSetupParent009Ops.drop 152) 85 150
  dsimp only at hm
  rw [←hs,hl] at hm
  have hf : nativeSetupParent009Ops=.const 2::nativeSetupParent009Ops.drop 1 := by decide +kernel
  have hfl : (nativeSetupParent009Ops.drop 1).length=678 := by decide +kernel
  have hc := parent_row_program_first_constant
    (nativeSetupInputReal nativeSetupParent009A0 nativeSetupParent009Xi0) 2 (nativeSetupParent009Ops.drop 1)
  rw [←hf,hfl] at hc
  simp only [nativeSetupParent009B0R,nativeSetupParent009FieldsR,List.getD_cons_zero,nativeSetupParent009Real]
  rw [hm]
  norm_num only [Nat.reduceAdd] at hc ⊢
  rw [hc]
  ring

/-- The depth-10 flat baseline is exactly twice the stored full variance. -/
theorem parent_row_baseline_010 :
    nativeSetupParent010B0R=2*nativeSetupParent010FieldsR.getD 0 0 := by
  have hs : nativeSetupParent010Ops=nativeSetupParent010Ops.take 162++
      (.mul (.var 91) (.var 161)::nativeSetupParent010Ops.drop 163) := by decide +kernel
  have hl : (nativeSetupParent010Ops.drop 163).length=547 := by decide +kernel
  have hm := parent_row_program_mul (nativeSetupInputReal nativeSetupParent010A0 nativeSetupParent010Xi0)
    (nativeSetupParent010Ops.take 162) (nativeSetupParent010Ops.drop 163) 91 161
  dsimp only at hm
  rw [←hs,hl] at hm
  have hf : nativeSetupParent010Ops=.const 2::nativeSetupParent010Ops.drop 1 := by decide +kernel
  have hfl : (nativeSetupParent010Ops.drop 1).length=709 := by decide +kernel
  have hc := parent_row_program_first_constant
    (nativeSetupInputReal nativeSetupParent010A0 nativeSetupParent010Xi0) 2 (nativeSetupParent010Ops.drop 1)
  rw [←hf,hfl] at hc
  simp only [nativeSetupParent010B0R,nativeSetupParent010FieldsR,List.getD_cons_zero,nativeSetupParent010Real]
  rw [hm]
  norm_num only [Nat.reduceAdd] at hc ⊢
  rw [hc]
  ring

/-- The depth-11 flat baseline is exactly twice the stored full variance. -/
theorem parent_row_baseline_011 :
    nativeSetupParent011B0R=2*nativeSetupParent011FieldsR.getD 0 0 := by
  have hs : nativeSetupParent011Ops=nativeSetupParent011Ops.take 172++
      (.mul (.var 96) (.var 171)::nativeSetupParent011Ops.drop 173) := by decide +kernel
  have hl : (nativeSetupParent011Ops.drop 173).length=567 := by decide +kernel
  have hm := parent_row_program_mul (nativeSetupInputReal nativeSetupParent011A0 nativeSetupParent011Xi0)
    (nativeSetupParent011Ops.take 172) (nativeSetupParent011Ops.drop 173) 96 171
  dsimp only at hm
  rw [←hs,hl] at hm
  have hf : nativeSetupParent011Ops=.const 2::nativeSetupParent011Ops.drop 1 := by decide +kernel
  have hfl : (nativeSetupParent011Ops.drop 1).length=739 := by decide +kernel
  have hc := parent_row_program_first_constant
    (nativeSetupInputReal nativeSetupParent011A0 nativeSetupParent011Xi0) 2 (nativeSetupParent011Ops.drop 1)
  rw [←hf,hfl] at hc
  simp only [nativeSetupParent011B0R,nativeSetupParent011FieldsR,List.getD_cons_zero,nativeSetupParent011Real]
  rw [hm]
  norm_num only [Nat.reduceAdd] at hc ⊢
  rw [hc]
  ring

/-- The depth-12 flat baseline is exactly twice the stored full variance. -/
theorem parent_row_baseline_012 :
    nativeSetupParent012B0R=2*nativeSetupParent012FieldsR.getD 0 0 := by
  have hs : nativeSetupParent012Ops=nativeSetupParent012Ops.take 183++
      (.mul (.var 102) (.var 182)::nativeSetupParent012Ops.drop 184) := by decide +kernel
  have hl : (nativeSetupParent012Ops.drop 184).length=587 := by decide +kernel
  have hm := parent_row_program_mul (nativeSetupInputReal nativeSetupParent012A0 nativeSetupParent012Xi0)
    (nativeSetupParent012Ops.take 183) (nativeSetupParent012Ops.drop 184) 102 182
  dsimp only at hm
  rw [←hs,hl] at hm
  have hf : nativeSetupParent012Ops=.const 2::nativeSetupParent012Ops.drop 1 := by decide +kernel
  have hfl : (nativeSetupParent012Ops.drop 1).length=770 := by decide +kernel
  have hc := parent_row_program_first_constant
    (nativeSetupInputReal nativeSetupParent012A0 nativeSetupParent012Xi0) 2 (nativeSetupParent012Ops.drop 1)
  rw [←hf,hfl] at hc
  simp only [nativeSetupParent012B0R,nativeSetupParent012FieldsR,List.getD_cons_zero,nativeSetupParent012Real]
  rw [hm]
  norm_num only [Nat.reduceAdd] at hc ⊢
  rw [hc]
  ring

/-- The depth-13 flat baseline is exactly twice the stored full variance. -/
theorem parent_row_baseline_013 :
    nativeSetupParent013B0R=2*nativeSetupParent013FieldsR.getD 0 0 := by
  have hs : nativeSetupParent013Ops=nativeSetupParent013Ops.take 193++
      (.mul (.var 107) (.var 192)::nativeSetupParent013Ops.drop 194) := by decide +kernel
  have hl : (nativeSetupParent013Ops.drop 194).length=607 := by decide +kernel
  have hm := parent_row_program_mul (nativeSetupInputReal nativeSetupParent013A0 nativeSetupParent013Xi0)
    (nativeSetupParent013Ops.take 193) (nativeSetupParent013Ops.drop 194) 107 192
  dsimp only at hm
  rw [←hs,hl] at hm
  have hf : nativeSetupParent013Ops=.const 2::nativeSetupParent013Ops.drop 1 := by decide +kernel
  have hfl : (nativeSetupParent013Ops.drop 1).length=800 := by decide +kernel
  have hc := parent_row_program_first_constant
    (nativeSetupInputReal nativeSetupParent013A0 nativeSetupParent013Xi0) 2 (nativeSetupParent013Ops.drop 1)
  rw [←hf,hfl] at hc
  simp only [nativeSetupParent013B0R,nativeSetupParent013FieldsR,List.getD_cons_zero,nativeSetupParent013Real]
  rw [hm]
  norm_num only [Nat.reduceAdd] at hc ⊢
  rw [hc]
  ring

/-- The depth-14 flat baseline is exactly twice the stored full variance. -/
theorem parent_row_baseline_014 :
    nativeSetupParent014B0R=2*nativeSetupParent014FieldsR.getD 0 0 := by
  have hs : nativeSetupParent014Ops=nativeSetupParent014Ops.take 204++
      (.mul (.var 113) (.var 203)::nativeSetupParent014Ops.drop 205) := by decide +kernel
  have hl : (nativeSetupParent014Ops.drop 205).length=627 := by decide +kernel
  have hm := parent_row_program_mul (nativeSetupInputReal nativeSetupParent014A0 nativeSetupParent014Xi0)
    (nativeSetupParent014Ops.take 204) (nativeSetupParent014Ops.drop 205) 113 203
  dsimp only at hm
  rw [←hs,hl] at hm
  have hf : nativeSetupParent014Ops=.const 2::nativeSetupParent014Ops.drop 1 := by decide +kernel
  have hfl : (nativeSetupParent014Ops.drop 1).length=831 := by decide +kernel
  have hc := parent_row_program_first_constant
    (nativeSetupInputReal nativeSetupParent014A0 nativeSetupParent014Xi0) 2 (nativeSetupParent014Ops.drop 1)
  rw [←hf,hfl] at hc
  simp only [nativeSetupParent014B0R,nativeSetupParent014FieldsR,List.getD_cons_zero,nativeSetupParent014Real]
  rw [hm]
  norm_num only [Nat.reduceAdd] at hc ⊢
  rw [hc]
  ring

/-- The depth-15 flat baseline is exactly twice the stored full variance. -/
theorem parent_row_baseline_015 :
    nativeSetupParent015B0R=2*nativeSetupParent015FieldsR.getD 0 0 := by
  have hs : nativeSetupParent015Ops=nativeSetupParent015Ops.take 214++
      (.mul (.var 118) (.var 213)::nativeSetupParent015Ops.drop 215) := by decide +kernel
  have hl : (nativeSetupParent015Ops.drop 215).length=647 := by decide +kernel
  have hm := parent_row_program_mul (nativeSetupInputReal nativeSetupParent015A0 nativeSetupParent015Xi0)
    (nativeSetupParent015Ops.take 214) (nativeSetupParent015Ops.drop 215) 118 213
  dsimp only at hm
  rw [←hs,hl] at hm
  have hf : nativeSetupParent015Ops=.const 2::nativeSetupParent015Ops.drop 1 := by decide +kernel
  have hfl : (nativeSetupParent015Ops.drop 1).length=861 := by decide +kernel
  have hc := parent_row_program_first_constant
    (nativeSetupInputReal nativeSetupParent015A0 nativeSetupParent015Xi0) 2 (nativeSetupParent015Ops.drop 1)
  rw [←hf,hfl] at hc
  simp only [nativeSetupParent015B0R,nativeSetupParent015FieldsR,List.getD_cons_zero,nativeSetupParent015Real]
  rw [hm]
  norm_num only [Nat.reduceAdd] at hc ⊢
  rw [hc]
  ring

/-- The depth-16 flat baseline is exactly twice the stored full variance. -/
theorem parent_row_baseline_016 :
    nativeSetupParent016B0R=2*nativeSetupParent016FieldsR.getD 0 0 := by
  have hs : nativeSetupParent016Ops=nativeSetupParent016Ops.take 225++
      (.mul (.var 124) (.var 224)::nativeSetupParent016Ops.drop 226) := by decide +kernel
  have hl : (nativeSetupParent016Ops.drop 226).length=667 := by decide +kernel
  have hm := parent_row_program_mul (nativeSetupInputReal nativeSetupParent016A0 nativeSetupParent016Xi0)
    (nativeSetupParent016Ops.take 225) (nativeSetupParent016Ops.drop 226) 124 224
  dsimp only at hm
  rw [←hs,hl] at hm
  have hf : nativeSetupParent016Ops=.const 2::nativeSetupParent016Ops.drop 1 := by decide +kernel
  have hfl : (nativeSetupParent016Ops.drop 1).length=892 := by decide +kernel
  have hc := parent_row_program_first_constant
    (nativeSetupInputReal nativeSetupParent016A0 nativeSetupParent016Xi0) 2 (nativeSetupParent016Ops.drop 1)
  rw [←hf,hfl] at hc
  simp only [nativeSetupParent016B0R,nativeSetupParent016FieldsR,List.getD_cons_zero,nativeSetupParent016Real]
  rw [hm]
  norm_num only [Nat.reduceAdd] at hc ⊢
  rw [hc]
  ring

end
end ASDExplicitGamma.Native
