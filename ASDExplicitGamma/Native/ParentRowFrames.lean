module

public import ASDExplicitGamma.Native.ParentRowCertificates
public import ASDExplicitGamma.Native.OldSignedQ1VarianceClock

/-! Exact frame extraction without expanding unrelated source-program nodes. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native Numerics.Mirror
noncomputable section

private theorem frame_instruction (inputs : List ℝ) (programHead : List Expr) (q : ℚ) :
    (nativePlanReal (nativePlanReal inputs programHead)
      [.const q, .mul (.var (programHead.length+3)) (.var 0), .exp (.var 0)]).getD 0 0 =
      Real.exp (inputs.getD 2 0*(q:ℝ)) := by
  simp only [nativePlanReal,evalReal,List.getD_cons_zero,List.getD_cons_succ,
    show programHead.length+3=(programHead.length+2)+1 by omega]
  rw [old_signed_plan_real_tail]

/-- The depth-1 frame is the exact endpoint exponential. -/
theorem parent_row_frame_001 :
    nativeSetupParent001FrameR = (3:ℝ)^(2*gammaZero*(1:ℝ)) := by
  let programHead := nativeSetupParent001Ops.take 19
  let tail : List Expr := [.const (17/25000:ℚ),
    .mul (.var (programHead.length+3)) (.var 0), .exp (.var 0)]
  have hsplit : nativeSetupParent001Ops=(programHead++tail)++nativeSetupParent001Ops.drop 22 := by
    decide +kernel
  have hlen : (nativeSetupParent001Ops.drop 22).length=423 := by decide +kernel
  unfold nativeSetupParent001FrameR nativeSetupParent001Real
  rw [hsplit,nativePlanReal_append]
  have hh := old_signed_plan_real_tail
    (nativePlanReal (nativeSetupInputReal nativeSetupParent001A0 nativeSetupParent001Xi0) (programHead++tail))
    (nativeSetupParent001Ops.drop 22) 0
  simp only [hlen,Nat.add_zero] at hh
  rw [hh,nativePlanReal_append]
  rw [show tail=[.const (17/25000:ℚ),.mul (.var (programHead.length+3)) (.var 0),.exp (.var 0)] from rfl,
    frame_instruction]
  simp only [nativeSetupInputReal,List.getD_cons_succ,List.getD_cons_zero]
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3)]
  norm_num [gammaZero]

/-- The depth-2 frame is the exact endpoint exponential. -/
theorem parent_row_frame_002 :
    nativeSetupParent002FrameR = (3:ℝ)^(2*gammaZero*(2:ℝ)) := by
  let programHead := nativeSetupParent002Ops.take 24
  let tail : List Expr := [.const (17/12500:ℚ),
    .mul (.var (programHead.length+3)) (.var 0), .exp (.var 0)]
  have hsplit : nativeSetupParent002Ops=(programHead++tail)++nativeSetupParent002Ops.drop 27 := by
    decide +kernel
  have hlen : (nativeSetupParent002Ops.drop 27).length=446 := by decide +kernel
  unfold nativeSetupParent002FrameR nativeSetupParent002Real
  rw [hsplit,nativePlanReal_append]
  have hh := old_signed_plan_real_tail
    (nativePlanReal (nativeSetupInputReal nativeSetupParent002A0 nativeSetupParent002Xi0) (programHead++tail))
    (nativeSetupParent002Ops.drop 27) 0
  simp only [hlen,Nat.add_zero] at hh
  rw [hh,nativePlanReal_append]
  rw [show tail=[.const (17/12500:ℚ),.mul (.var (programHead.length+3)) (.var 0),.exp (.var 0)] from rfl,
    frame_instruction]
  simp only [nativeSetupInputReal,List.getD_cons_succ,List.getD_cons_zero]
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3)]
  norm_num [gammaZero]

/-- The depth-3 frame is the exact endpoint exponential. -/
theorem parent_row_frame_003 :
    nativeSetupParent003FrameR = (3:ℝ)^(2*gammaZero*(3:ℝ)) := by
  let programHead := nativeSetupParent003Ops.take 28
  let tail : List Expr := [.const (51/25000:ℚ),
    .mul (.var (programHead.length+3)) (.var 0), .exp (.var 0)]
  have hsplit : nativeSetupParent003Ops=(programHead++tail)++nativeSetupParent003Ops.drop 31 := by
    decide +kernel
  have hlen : (nativeSetupParent003Ops.drop 31).length=470 := by decide +kernel
  unfold nativeSetupParent003FrameR nativeSetupParent003Real
  rw [hsplit,nativePlanReal_append]
  have hh := old_signed_plan_real_tail
    (nativePlanReal (nativeSetupInputReal nativeSetupParent003A0 nativeSetupParent003Xi0) (programHead++tail))
    (nativeSetupParent003Ops.drop 31) 0
  simp only [hlen,Nat.add_zero] at hh
  rw [hh,nativePlanReal_append]
  rw [show tail=[.const (51/25000:ℚ),.mul (.var (programHead.length+3)) (.var 0),.exp (.var 0)] from rfl,
    frame_instruction]
  simp only [nativeSetupInputReal,List.getD_cons_succ,List.getD_cons_zero]
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3)]
  norm_num [gammaZero]

/-- The depth-4 frame is the exact endpoint exponential. -/
theorem parent_row_frame_004 :
    nativeSetupParent004FrameR = (3:ℝ)^(2*gammaZero*(4:ℝ)) := by
  let programHead := nativeSetupParent004Ops.take 32
  let tail : List Expr := [.const (17/6250:ℚ),
    .mul (.var (programHead.length+3)) (.var 0), .exp (.var 0)]
  have hsplit : nativeSetupParent004Ops=(programHead++tail)++nativeSetupParent004Ops.drop 35 := by
    decide +kernel
  have hlen : (nativeSetupParent004Ops.drop 35).length=494 := by decide +kernel
  unfold nativeSetupParent004FrameR nativeSetupParent004Real
  rw [hsplit,nativePlanReal_append]
  have hh := old_signed_plan_real_tail
    (nativePlanReal (nativeSetupInputReal nativeSetupParent004A0 nativeSetupParent004Xi0) (programHead++tail))
    (nativeSetupParent004Ops.drop 35) 0
  simp only [hlen,Nat.add_zero] at hh
  rw [hh,nativePlanReal_append]
  rw [show tail=[.const (17/6250:ℚ),.mul (.var (programHead.length+3)) (.var 0),.exp (.var 0)] from rfl,
    frame_instruction]
  simp only [nativeSetupInputReal,List.getD_cons_succ,List.getD_cons_zero]
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3)]
  norm_num [gammaZero]

/-- The depth-5 frame is the exact endpoint exponential. -/
theorem parent_row_frame_005 :
    nativeSetupParent005FrameR = (3:ℝ)^(2*gammaZero*(5:ℝ)) := by
  let programHead := nativeSetupParent005Ops.take 36
  let tail : List Expr := [.const (17/5000:ℚ),
    .mul (.var (programHead.length+3)) (.var 0), .exp (.var 0)]
  have hsplit : nativeSetupParent005Ops=(programHead++tail)++nativeSetupParent005Ops.drop 39 := by
    decide +kernel
  have hlen : (nativeSetupParent005Ops.drop 39).length=518 := by decide +kernel
  unfold nativeSetupParent005FrameR nativeSetupParent005Real
  rw [hsplit,nativePlanReal_append]
  have hh := old_signed_plan_real_tail
    (nativePlanReal (nativeSetupInputReal nativeSetupParent005A0 nativeSetupParent005Xi0) (programHead++tail))
    (nativeSetupParent005Ops.drop 39) 0
  simp only [hlen,Nat.add_zero] at hh
  rw [hh,nativePlanReal_append]
  rw [show tail=[.const (17/5000:ℚ),.mul (.var (programHead.length+3)) (.var 0),.exp (.var 0)] from rfl,
    frame_instruction]
  simp only [nativeSetupInputReal,List.getD_cons_succ,List.getD_cons_zero]
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3)]
  norm_num [gammaZero]

/-- The depth-6 frame is the exact endpoint exponential. -/
theorem parent_row_frame_006 :
    nativeSetupParent006FrameR = (3:ℝ)^(2*gammaZero*(6:ℝ)) := by
  let programHead := nativeSetupParent006Ops.take 40
  let tail : List Expr := [.const (51/12500:ℚ),
    .mul (.var (programHead.length+3)) (.var 0), .exp (.var 0)]
  have hsplit : nativeSetupParent006Ops=(programHead++tail)++nativeSetupParent006Ops.drop 43 := by
    decide +kernel
  have hlen : (nativeSetupParent006Ops.drop 43).length=545 := by decide +kernel
  unfold nativeSetupParent006FrameR nativeSetupParent006Real
  rw [hsplit,nativePlanReal_append]
  have hh := old_signed_plan_real_tail
    (nativePlanReal (nativeSetupInputReal nativeSetupParent006A0 nativeSetupParent006Xi0) (programHead++tail))
    (nativeSetupParent006Ops.drop 43) 0
  simp only [hlen,Nat.add_zero] at hh
  rw [hh,nativePlanReal_append]
  rw [show tail=[.const (51/12500:ℚ),.mul (.var (programHead.length+3)) (.var 0),.exp (.var 0)] from rfl,
    frame_instruction]
  simp only [nativeSetupInputReal,List.getD_cons_succ,List.getD_cons_zero]
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3)]
  norm_num [gammaZero]

/-- The depth-7 frame is the exact endpoint exponential. -/
theorem parent_row_frame_007 :
    nativeSetupParent007FrameR = (3:ℝ)^(2*gammaZero*(7:ℝ)) := by
  let programHead := nativeSetupParent007Ops.take 44
  let tail : List Expr := [.const (119/25000:ℚ),
    .mul (.var (programHead.length+3)) (.var 0), .exp (.var 0)]
  have hsplit : nativeSetupParent007Ops=(programHead++tail)++nativeSetupParent007Ops.drop 47 := by
    decide +kernel
  have hlen : (nativeSetupParent007Ops.drop 47).length=571 := by decide +kernel
  unfold nativeSetupParent007FrameR nativeSetupParent007Real
  rw [hsplit,nativePlanReal_append]
  have hh := old_signed_plan_real_tail
    (nativePlanReal (nativeSetupInputReal nativeSetupParent007A0 nativeSetupParent007Xi0) (programHead++tail))
    (nativeSetupParent007Ops.drop 47) 0
  simp only [hlen,Nat.add_zero] at hh
  rw [hh,nativePlanReal_append]
  rw [show tail=[.const (119/25000:ℚ),.mul (.var (programHead.length+3)) (.var 0),.exp (.var 0)] from rfl,
    frame_instruction]
  simp only [nativeSetupInputReal,List.getD_cons_succ,List.getD_cons_zero]
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3)]
  norm_num [gammaZero]

/-- The depth-8 frame is the exact endpoint exponential. -/
theorem parent_row_frame_008 :
    nativeSetupParent008FrameR = (3:ℝ)^(2*gammaZero*(8:ℝ)) := by
  let programHead := nativeSetupParent008Ops.take 48
  let tail : List Expr := [.const (17/3125:ℚ),
    .mul (.var (programHead.length+3)) (.var 0), .exp (.var 0)]
  have hsplit : nativeSetupParent008Ops=(programHead++tail)++nativeSetupParent008Ops.drop 51 := by
    decide +kernel
  have hlen : (nativeSetupParent008Ops.drop 51).length=598 := by decide +kernel
  unfold nativeSetupParent008FrameR nativeSetupParent008Real
  rw [hsplit,nativePlanReal_append]
  have hh := old_signed_plan_real_tail
    (nativePlanReal (nativeSetupInputReal nativeSetupParent008A0 nativeSetupParent008Xi0) (programHead++tail))
    (nativeSetupParent008Ops.drop 51) 0
  simp only [hlen,Nat.add_zero] at hh
  rw [hh,nativePlanReal_append]
  rw [show tail=[.const (17/3125:ℚ),.mul (.var (programHead.length+3)) (.var 0),.exp (.var 0)] from rfl,
    frame_instruction]
  simp only [nativeSetupInputReal,List.getD_cons_succ,List.getD_cons_zero]
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3)]
  norm_num [gammaZero]

/-- The depth-9 frame is the exact endpoint exponential. -/
theorem parent_row_frame_009 :
    nativeSetupParent009FrameR = (3:ℝ)^(2*gammaZero*(9:ℝ)) := by
  let programHead := nativeSetupParent009Ops.take 52
  let tail : List Expr := [.const (153/25000:ℚ),
    .mul (.var (programHead.length+3)) (.var 0), .exp (.var 0)]
  have hsplit : nativeSetupParent009Ops=(programHead++tail)++nativeSetupParent009Ops.drop 55 := by
    decide +kernel
  have hlen : (nativeSetupParent009Ops.drop 55).length=624 := by decide +kernel
  unfold nativeSetupParent009FrameR nativeSetupParent009Real
  rw [hsplit,nativePlanReal_append]
  have hh := old_signed_plan_real_tail
    (nativePlanReal (nativeSetupInputReal nativeSetupParent009A0 nativeSetupParent009Xi0) (programHead++tail))
    (nativeSetupParent009Ops.drop 55) 0
  simp only [hlen,Nat.add_zero] at hh
  rw [hh,nativePlanReal_append]
  rw [show tail=[.const (153/25000:ℚ),.mul (.var (programHead.length+3)) (.var 0),.exp (.var 0)] from rfl,
    frame_instruction]
  simp only [nativeSetupInputReal,List.getD_cons_succ,List.getD_cons_zero]
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3)]
  norm_num [gammaZero]

/-- The depth-10 frame is the exact endpoint exponential. -/
theorem parent_row_frame_010 :
    nativeSetupParent010FrameR = (3:ℝ)^(2*gammaZero*(10:ℝ)) := by
  let programHead := nativeSetupParent010Ops.take 56
  let tail : List Expr := [.const (17/2500:ℚ),
    .mul (.var (programHead.length+3)) (.var 0), .exp (.var 0)]
  have hsplit : nativeSetupParent010Ops=(programHead++tail)++nativeSetupParent010Ops.drop 59 := by
    decide +kernel
  have hlen : (nativeSetupParent010Ops.drop 59).length=651 := by decide +kernel
  unfold nativeSetupParent010FrameR nativeSetupParent010Real
  rw [hsplit,nativePlanReal_append]
  have hh := old_signed_plan_real_tail
    (nativePlanReal (nativeSetupInputReal nativeSetupParent010A0 nativeSetupParent010Xi0) (programHead++tail))
    (nativeSetupParent010Ops.drop 59) 0
  simp only [hlen,Nat.add_zero] at hh
  rw [hh,nativePlanReal_append]
  rw [show tail=[.const (17/2500:ℚ),.mul (.var (programHead.length+3)) (.var 0),.exp (.var 0)] from rfl,
    frame_instruction]
  simp only [nativeSetupInputReal,List.getD_cons_succ,List.getD_cons_zero]
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3)]
  norm_num [gammaZero]

/-- The depth-11 frame is the exact endpoint exponential. -/
theorem parent_row_frame_011 :
    nativeSetupParent011FrameR = (3:ℝ)^(2*gammaZero*(11:ℝ)) := by
  let programHead := nativeSetupParent011Ops.take 60
  let tail : List Expr := [.const (187/25000:ℚ),
    .mul (.var (programHead.length+3)) (.var 0), .exp (.var 0)]
  have hsplit : nativeSetupParent011Ops=(programHead++tail)++nativeSetupParent011Ops.drop 63 := by
    decide +kernel
  have hlen : (nativeSetupParent011Ops.drop 63).length=677 := by decide +kernel
  unfold nativeSetupParent011FrameR nativeSetupParent011Real
  rw [hsplit,nativePlanReal_append]
  have hh := old_signed_plan_real_tail
    (nativePlanReal (nativeSetupInputReal nativeSetupParent011A0 nativeSetupParent011Xi0) (programHead++tail))
    (nativeSetupParent011Ops.drop 63) 0
  simp only [hlen,Nat.add_zero] at hh
  rw [hh,nativePlanReal_append]
  rw [show tail=[.const (187/25000:ℚ),.mul (.var (programHead.length+3)) (.var 0),.exp (.var 0)] from rfl,
    frame_instruction]
  simp only [nativeSetupInputReal,List.getD_cons_succ,List.getD_cons_zero]
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3)]
  norm_num [gammaZero]

/-- The depth-12 frame is the exact endpoint exponential. -/
theorem parent_row_frame_012 :
    nativeSetupParent012FrameR = (3:ℝ)^(2*gammaZero*(12:ℝ)) := by
  let programHead := nativeSetupParent012Ops.take 64
  let tail : List Expr := [.const (51/6250:ℚ),
    .mul (.var (programHead.length+3)) (.var 0), .exp (.var 0)]
  have hsplit : nativeSetupParent012Ops=(programHead++tail)++nativeSetupParent012Ops.drop 67 := by
    decide +kernel
  have hlen : (nativeSetupParent012Ops.drop 67).length=704 := by decide +kernel
  unfold nativeSetupParent012FrameR nativeSetupParent012Real
  rw [hsplit,nativePlanReal_append]
  have hh := old_signed_plan_real_tail
    (nativePlanReal (nativeSetupInputReal nativeSetupParent012A0 nativeSetupParent012Xi0) (programHead++tail))
    (nativeSetupParent012Ops.drop 67) 0
  simp only [hlen,Nat.add_zero] at hh
  rw [hh,nativePlanReal_append]
  rw [show tail=[.const (51/6250:ℚ),.mul (.var (programHead.length+3)) (.var 0),.exp (.var 0)] from rfl,
    frame_instruction]
  simp only [nativeSetupInputReal,List.getD_cons_succ,List.getD_cons_zero]
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3)]
  norm_num [gammaZero]

/-- The depth-13 frame is the exact endpoint exponential. -/
theorem parent_row_frame_013 :
    nativeSetupParent013FrameR = (3:ℝ)^(2*gammaZero*(13:ℝ)) := by
  let programHead := nativeSetupParent013Ops.take 68
  let tail : List Expr := [.const (221/25000:ℚ),
    .mul (.var (programHead.length+3)) (.var 0), .exp (.var 0)]
  have hsplit : nativeSetupParent013Ops=(programHead++tail)++nativeSetupParent013Ops.drop 71 := by
    decide +kernel
  have hlen : (nativeSetupParent013Ops.drop 71).length=730 := by decide +kernel
  unfold nativeSetupParent013FrameR nativeSetupParent013Real
  rw [hsplit,nativePlanReal_append]
  have hh := old_signed_plan_real_tail
    (nativePlanReal (nativeSetupInputReal nativeSetupParent013A0 nativeSetupParent013Xi0) (programHead++tail))
    (nativeSetupParent013Ops.drop 71) 0
  simp only [hlen,Nat.add_zero] at hh
  rw [hh,nativePlanReal_append]
  rw [show tail=[.const (221/25000:ℚ),.mul (.var (programHead.length+3)) (.var 0),.exp (.var 0)] from rfl,
    frame_instruction]
  simp only [nativeSetupInputReal,List.getD_cons_succ,List.getD_cons_zero]
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3)]
  norm_num [gammaZero]

/-- The depth-14 frame is the exact endpoint exponential. -/
theorem parent_row_frame_014 :
    nativeSetupParent014FrameR = (3:ℝ)^(2*gammaZero*(14:ℝ)) := by
  let programHead := nativeSetupParent014Ops.take 72
  let tail : List Expr := [.const (119/12500:ℚ),
    .mul (.var (programHead.length+3)) (.var 0), .exp (.var 0)]
  have hsplit : nativeSetupParent014Ops=(programHead++tail)++nativeSetupParent014Ops.drop 75 := by
    decide +kernel
  have hlen : (nativeSetupParent014Ops.drop 75).length=757 := by decide +kernel
  unfold nativeSetupParent014FrameR nativeSetupParent014Real
  rw [hsplit,nativePlanReal_append]
  have hh := old_signed_plan_real_tail
    (nativePlanReal (nativeSetupInputReal nativeSetupParent014A0 nativeSetupParent014Xi0) (programHead++tail))
    (nativeSetupParent014Ops.drop 75) 0
  simp only [hlen,Nat.add_zero] at hh
  rw [hh,nativePlanReal_append]
  rw [show tail=[.const (119/12500:ℚ),.mul (.var (programHead.length+3)) (.var 0),.exp (.var 0)] from rfl,
    frame_instruction]
  simp only [nativeSetupInputReal,List.getD_cons_succ,List.getD_cons_zero]
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3)]
  norm_num [gammaZero]

/-- The depth-15 frame is the exact endpoint exponential. -/
theorem parent_row_frame_015 :
    nativeSetupParent015FrameR = (3:ℝ)^(2*gammaZero*(15:ℝ)) := by
  let programHead := nativeSetupParent015Ops.take 76
  let tail : List Expr := [.const (51/5000:ℚ),
    .mul (.var (programHead.length+3)) (.var 0), .exp (.var 0)]
  have hsplit : nativeSetupParent015Ops=(programHead++tail)++nativeSetupParent015Ops.drop 79 := by
    decide +kernel
  have hlen : (nativeSetupParent015Ops.drop 79).length=783 := by decide +kernel
  unfold nativeSetupParent015FrameR nativeSetupParent015Real
  rw [hsplit,nativePlanReal_append]
  have hh := old_signed_plan_real_tail
    (nativePlanReal (nativeSetupInputReal nativeSetupParent015A0 nativeSetupParent015Xi0) (programHead++tail))
    (nativeSetupParent015Ops.drop 79) 0
  simp only [hlen,Nat.add_zero] at hh
  rw [hh,nativePlanReal_append]
  rw [show tail=[.const (51/5000:ℚ),.mul (.var (programHead.length+3)) (.var 0),.exp (.var 0)] from rfl,
    frame_instruction]
  simp only [nativeSetupInputReal,List.getD_cons_succ,List.getD_cons_zero]
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3)]
  norm_num [gammaZero]

/-- The depth-16 frame is the exact endpoint exponential. -/
theorem parent_row_frame_016 :
    nativeSetupParent016FrameR = (3:ℝ)^(2*gammaZero*(16:ℝ)) := by
  let programHead := nativeSetupParent016Ops.take 80
  let tail : List Expr := [.const (34/3125:ℚ),
    .mul (.var (programHead.length+3)) (.var 0), .exp (.var 0)]
  have hsplit : nativeSetupParent016Ops=(programHead++tail)++nativeSetupParent016Ops.drop 83 := by
    decide +kernel
  have hlen : (nativeSetupParent016Ops.drop 83).length=810 := by decide +kernel
  unfold nativeSetupParent016FrameR nativeSetupParent016Real
  rw [hsplit,nativePlanReal_append]
  have hh := old_signed_plan_real_tail
    (nativePlanReal (nativeSetupInputReal nativeSetupParent016A0 nativeSetupParent016Xi0) (programHead++tail))
    (nativeSetupParent016Ops.drop 83) 0
  simp only [hlen,Nat.add_zero] at hh
  rw [hh,nativePlanReal_append]
  rw [show tail=[.const (34/3125:ℚ),.mul (.var (programHead.length+3)) (.var 0),.exp (.var 0)] from rfl,
    frame_instruction]
  simp only [nativeSetupInputReal,List.getD_cons_succ,List.getD_cons_zero]
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3)]
  norm_num [gammaZero]

end
end ASDExplicitGamma.Native
