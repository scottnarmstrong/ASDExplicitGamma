module

public import ASDExplicitGamma.Native.ParentRowCertificates
public import ASDExplicitGamma.Native.ParentRowProgram
public import ASDExplicitGamma.Native.OldSignedGenericShortMean

/-! Exact initial-mean fields and their actual generic producer payment. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native
noncomputable section

/-- The depth-1 setup preserves its exact initial mean input. -/
theorem parent_row_initial_mean_001 :
    nativeSetupParent001FieldsR.getD 14 0=(nativeSetupParent001A0:ℝ) := by
  have hh := old_signed_plan_real_tail
    (nativeSetupInputReal nativeSetupParent001A0 nativeSetupParent001Xi0) nativeSetupParent001Ops 1
  have hl : nativeSetupParent001Ops.length+1=446 := by decide +kernel
  rw [hl] at hh
  simpa only [nativeSetupParent001FieldsR,nativeSetupParent001Real,nativeSetupInputReal,
    List.getD_cons_zero,List.getD_cons_succ] using hh

/-- The depth-2 setup preserves its exact initial mean input. -/
theorem parent_row_initial_mean_002 :
    nativeSetupParent002FieldsR.getD 14 0=(nativeSetupParent001A0:ℝ) := by
  have hh := old_signed_plan_real_tail
    (nativeSetupInputReal nativeSetupParent002A0 nativeSetupParent002Xi0) nativeSetupParent002Ops 1
  have hl : nativeSetupParent002Ops.length+1=474 := by decide +kernel
  rw [hl] at hh
  have ha : nativeSetupParent002A0=nativeSetupParent001A0 := by decide +kernel
  simpa only [nativeSetupParent002FieldsR,nativeSetupParent002Real,nativeSetupInputReal,
    List.getD_cons_zero,List.getD_cons_succ,ha] using hh

/-- The depth-3 setup preserves its exact initial mean input. -/
theorem parent_row_initial_mean_003 :
    nativeSetupParent003FieldsR.getD 14 0=(nativeSetupParent001A0:ℝ) := by
  have hh := old_signed_plan_real_tail
    (nativeSetupInputReal nativeSetupParent003A0 nativeSetupParent003Xi0) nativeSetupParent003Ops 1
  have hl : nativeSetupParent003Ops.length+1=502 := by decide +kernel
  rw [hl] at hh
  have ha : nativeSetupParent003A0=nativeSetupParent001A0 := by decide +kernel
  simpa only [nativeSetupParent003FieldsR,nativeSetupParent003Real,nativeSetupInputReal,
    List.getD_cons_zero,List.getD_cons_succ,ha] using hh

/-- The depth-4 setup preserves its exact initial mean input. -/
theorem parent_row_initial_mean_004 :
    nativeSetupParent004FieldsR.getD 14 0=(nativeSetupParent001A0:ℝ) := by
  have hh := old_signed_plan_real_tail
    (nativeSetupInputReal nativeSetupParent004A0 nativeSetupParent004Xi0) nativeSetupParent004Ops 1
  have hl : nativeSetupParent004Ops.length+1=530 := by decide +kernel
  rw [hl] at hh
  have ha : nativeSetupParent004A0=nativeSetupParent001A0 := by decide +kernel
  simpa only [nativeSetupParent004FieldsR,nativeSetupParent004Real,nativeSetupInputReal,
    List.getD_cons_zero,List.getD_cons_succ,ha] using hh

/-- The depth-5 setup preserves its exact initial mean input. -/
theorem parent_row_initial_mean_005 :
    nativeSetupParent005FieldsR.getD 14 0=(nativeSetupParent001A0:ℝ) := by
  have hh := old_signed_plan_real_tail
    (nativeSetupInputReal nativeSetupParent005A0 nativeSetupParent005Xi0) nativeSetupParent005Ops 1
  have hl : nativeSetupParent005Ops.length+1=558 := by decide +kernel
  rw [hl] at hh
  have ha : nativeSetupParent005A0=nativeSetupParent001A0 := by decide +kernel
  simpa only [nativeSetupParent005FieldsR,nativeSetupParent005Real,nativeSetupInputReal,
    List.getD_cons_zero,List.getD_cons_succ,ha] using hh

/-- The depth-6 setup preserves its exact initial mean input. -/
theorem parent_row_initial_mean_006 :
    nativeSetupParent006FieldsR.getD 14 0=(nativeSetupParent001A0:ℝ) := by
  have hh := old_signed_plan_real_tail
    (nativeSetupInputReal nativeSetupParent006A0 nativeSetupParent006Xi0) nativeSetupParent006Ops 1
  have hl : nativeSetupParent006Ops.length+1=589 := by decide +kernel
  rw [hl] at hh
  have ha : nativeSetupParent006A0=nativeSetupParent001A0 := by decide +kernel
  simpa only [nativeSetupParent006FieldsR,nativeSetupParent006Real,nativeSetupInputReal,
    List.getD_cons_zero,List.getD_cons_succ,ha] using hh

/-- The depth-7 setup preserves its exact initial mean input. -/
theorem parent_row_initial_mean_007 :
    nativeSetupParent007FieldsR.getD 14 0=(nativeSetupParent001A0:ℝ) := by
  have hh := old_signed_plan_real_tail
    (nativeSetupInputReal nativeSetupParent007A0 nativeSetupParent007Xi0) nativeSetupParent007Ops 1
  have hl : nativeSetupParent007Ops.length+1=619 := by decide +kernel
  rw [hl] at hh
  have ha : nativeSetupParent007A0=nativeSetupParent001A0 := by decide +kernel
  simpa only [nativeSetupParent007FieldsR,nativeSetupParent007Real,nativeSetupInputReal,
    List.getD_cons_zero,List.getD_cons_succ,ha] using hh

/-- The depth-8 setup preserves its exact initial mean input. -/
theorem parent_row_initial_mean_008 :
    nativeSetupParent008FieldsR.getD 14 0=(nativeSetupParent001A0:ℝ) := by
  have hh := old_signed_plan_real_tail
    (nativeSetupInputReal nativeSetupParent008A0 nativeSetupParent008Xi0) nativeSetupParent008Ops 1
  have hl : nativeSetupParent008Ops.length+1=650 := by decide +kernel
  rw [hl] at hh
  have ha : nativeSetupParent008A0=nativeSetupParent001A0 := by decide +kernel
  simpa only [nativeSetupParent008FieldsR,nativeSetupParent008Real,nativeSetupInputReal,
    List.getD_cons_zero,List.getD_cons_succ,ha] using hh

/-- The depth-9 setup preserves its exact initial mean input. -/
theorem parent_row_initial_mean_009 :
    nativeSetupParent009FieldsR.getD 14 0=(nativeSetupParent001A0:ℝ) := by
  have hh := old_signed_plan_real_tail
    (nativeSetupInputReal nativeSetupParent009A0 nativeSetupParent009Xi0) nativeSetupParent009Ops 1
  have hl : nativeSetupParent009Ops.length+1=680 := by decide +kernel
  rw [hl] at hh
  have ha : nativeSetupParent009A0=nativeSetupParent001A0 := by decide +kernel
  simpa only [nativeSetupParent009FieldsR,nativeSetupParent009Real,nativeSetupInputReal,
    List.getD_cons_zero,List.getD_cons_succ,ha] using hh

/-- The depth-10 setup preserves its exact initial mean input. -/
theorem parent_row_initial_mean_010 :
    nativeSetupParent010FieldsR.getD 14 0=(nativeSetupParent001A0:ℝ) := by
  have hh := old_signed_plan_real_tail
    (nativeSetupInputReal nativeSetupParent010A0 nativeSetupParent010Xi0) nativeSetupParent010Ops 1
  have hl : nativeSetupParent010Ops.length+1=711 := by decide +kernel
  rw [hl] at hh
  have ha : nativeSetupParent010A0=nativeSetupParent001A0 := by decide +kernel
  simpa only [nativeSetupParent010FieldsR,nativeSetupParent010Real,nativeSetupInputReal,
    List.getD_cons_zero,List.getD_cons_succ,ha] using hh

/-- The depth-11 setup preserves its exact initial mean input. -/
theorem parent_row_initial_mean_011 :
    nativeSetupParent011FieldsR.getD 14 0=(nativeSetupParent001A0:ℝ) := by
  have hh := old_signed_plan_real_tail
    (nativeSetupInputReal nativeSetupParent011A0 nativeSetupParent011Xi0) nativeSetupParent011Ops 1
  have hl : nativeSetupParent011Ops.length+1=741 := by decide +kernel
  rw [hl] at hh
  have ha : nativeSetupParent011A0=nativeSetupParent001A0 := by decide +kernel
  simpa only [nativeSetupParent011FieldsR,nativeSetupParent011Real,nativeSetupInputReal,
    List.getD_cons_zero,List.getD_cons_succ,ha] using hh

/-- The depth-12 setup preserves its exact initial mean input. -/
theorem parent_row_initial_mean_012 :
    nativeSetupParent012FieldsR.getD 14 0=(nativeSetupParent001A0:ℝ) := by
  have hh := old_signed_plan_real_tail
    (nativeSetupInputReal nativeSetupParent012A0 nativeSetupParent012Xi0) nativeSetupParent012Ops 1
  have hl : nativeSetupParent012Ops.length+1=772 := by decide +kernel
  rw [hl] at hh
  have ha : nativeSetupParent012A0=nativeSetupParent001A0 := by decide +kernel
  simpa only [nativeSetupParent012FieldsR,nativeSetupParent012Real,nativeSetupInputReal,
    List.getD_cons_zero,List.getD_cons_succ,ha] using hh

/-- The depth-13 setup preserves its exact initial mean input. -/
theorem parent_row_initial_mean_013 :
    nativeSetupParent013FieldsR.getD 14 0=(nativeSetupParent001A0:ℝ) := by
  have hh := old_signed_plan_real_tail
    (nativeSetupInputReal nativeSetupParent013A0 nativeSetupParent013Xi0) nativeSetupParent013Ops 1
  have hl : nativeSetupParent013Ops.length+1=802 := by decide +kernel
  rw [hl] at hh
  have ha : nativeSetupParent013A0=nativeSetupParent001A0 := by decide +kernel
  simpa only [nativeSetupParent013FieldsR,nativeSetupParent013Real,nativeSetupInputReal,
    List.getD_cons_zero,List.getD_cons_succ,ha] using hh

/-- The depth-14 setup preserves its exact initial mean input. -/
theorem parent_row_initial_mean_014 :
    nativeSetupParent014FieldsR.getD 14 0=(nativeSetupParent001A0:ℝ) := by
  have hh := old_signed_plan_real_tail
    (nativeSetupInputReal nativeSetupParent014A0 nativeSetupParent014Xi0) nativeSetupParent014Ops 1
  have hl : nativeSetupParent014Ops.length+1=833 := by decide +kernel
  rw [hl] at hh
  have ha : nativeSetupParent014A0=nativeSetupParent001A0 := by decide +kernel
  simpa only [nativeSetupParent014FieldsR,nativeSetupParent014Real,nativeSetupInputReal,
    List.getD_cons_zero,List.getD_cons_succ,ha] using hh

/-- The depth-15 setup preserves its exact initial mean input. -/
theorem parent_row_initial_mean_015 :
    nativeSetupParent015FieldsR.getD 14 0=(nativeSetupParent001A0:ℝ) := by
  have hh := old_signed_plan_real_tail
    (nativeSetupInputReal nativeSetupParent015A0 nativeSetupParent015Xi0) nativeSetupParent015Ops 1
  have hl : nativeSetupParent015Ops.length+1=863 := by decide +kernel
  rw [hl] at hh
  have ha : nativeSetupParent015A0=nativeSetupParent001A0 := by decide +kernel
  simpa only [nativeSetupParent015FieldsR,nativeSetupParent015Real,nativeSetupInputReal,
    List.getD_cons_zero,List.getD_cons_succ,ha] using hh

/-- The depth-16 setup preserves its exact initial mean input. -/
theorem parent_row_initial_mean_016 :
    nativeSetupParent016FieldsR.getD 14 0=(nativeSetupParent001A0:ℝ) := by
  have hh := old_signed_plan_real_tail
    (nativeSetupInputReal nativeSetupParent016A0 nativeSetupParent016Xi0) nativeSetupParent016Ops 1
  have hl : nativeSetupParent016Ops.length+1=894 := by decide +kernel
  rw [hl] at hh
  have ha : nativeSetupParent016A0=nativeSetupParent001A0 := by decide +kernel
  simpa only [nativeSetupParent016FieldsR,nativeSetupParent016Real,nativeSetupInputReal,
    List.getD_cons_zero,List.getD_cons_succ,ha] using hh

/-- Every parent panel uses the same certified initial mean input. -/
theorem parent_row_initial_mean_eq (j : Fin 16) :
    (parentRowFields j).getD 14 0=(nativeSetupParent001A0:ℝ) := by
  fin_cases j <;> simp only [parentRowFields,nativeConfiguredParentEndpoint,
    nativeParentEndpointCertificates,nativeParent001EndpointCertificate, nativeParent002EndpointCertificate, nativeParent003EndpointCertificate, nativeParent004EndpointCertificate, nativeParent005EndpointCertificate, nativeParent006EndpointCertificate, nativeParent007EndpointCertificate, nativeParent008EndpointCertificate, nativeParent009EndpointCertificate, nativeParent010EndpointCertificate, nativeParent011EndpointCertificate, nativeParent012EndpointCertificate, nativeParent013EndpointCertificate, nativeParent014EndpointCertificate, nativeParent015EndpointCertificate, nativeParent016EndpointCertificate,List.getD_cons_zero,List.getD_cons_succ]
  · exact parent_row_initial_mean_001
  · exact parent_row_initial_mean_002
  · exact parent_row_initial_mean_003
  · exact parent_row_initial_mean_004
  · exact parent_row_initial_mean_005
  · exact parent_row_initial_mean_006
  · exact parent_row_initial_mean_007
  · exact parent_row_initial_mean_008
  · exact parent_row_initial_mean_009
  · exact parent_row_initial_mean_010
  · exact parent_row_initial_mean_011
  · exact parent_row_initial_mean_012
  · exact parent_row_initial_mean_013
  · exact parent_row_initial_mean_014
  · exact parent_row_initial_mean_015
  · exact parent_row_initial_mean_016

/-- The existing generic mean producer at depth five fits the exact stored input. -/
theorem parent_row_generic_initial_mean_le (j : Fin 16) :
    nativeSourceGenericMeanProfile gammaZero 1 5≤(parentRowFields j).getD 14 0 := by
  rw [parent_row_initial_mean_eq]
  have hh := old_signed_generic_short_mean 5 (by norm_num)
  apply hh.trans
  norm_num [nativeSetupParent001A0]

end
end ASDExplicitGamma.Native
