module

public import ASDExplicitGamma.Native.ParentWeakFieldFieldsA
public import ASDExplicitGamma.Native.ParentWeakFieldFieldsB
public import ASDExplicitGamma.Native.ParentWeakFieldValue

/-! Exact selected weak slope and certified slack in the stored initial Xi. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics Numerics.Native Numerics.Mirror
noncomputable section

/-- Every selected weak slope is exactly its literal real source formula. -/
theorem parent_weak_field_slope_eq (j : Fin 16) :
    (parentRowFields j).getD 12 0=parentWeakFieldSlopeValue (j.val+1) := by
  fin_cases j <;> simp only [parentRowFields,nativeConfiguredParentEndpoint,nativeParentEndpointCertificates,nativeParent001EndpointCertificate,nativeParent002EndpointCertificate,nativeParent003EndpointCertificate,nativeParent004EndpointCertificate,nativeParent005EndpointCertificate,nativeParent006EndpointCertificate,nativeParent007EndpointCertificate,nativeParent008EndpointCertificate,nativeParent009EndpointCertificate,nativeParent010EndpointCertificate,nativeParent011EndpointCertificate,nativeParent012EndpointCertificate,nativeParent013EndpointCertificate,nativeParent014EndpointCertificate,nativeParent015EndpointCertificate,nativeParent016EndpointCertificate,List.getD_cons_zero,List.getD_cons_succ]
  · exact parent_weak_field_slope_001.trans (parent_weak_field_expr_eval _ (by rfl) 1)
  · exact parent_weak_field_slope_002.trans (parent_weak_field_expr_eval _ (by rfl) 2)
  · exact parent_weak_field_slope_003.trans (parent_weak_field_expr_eval _ (by rfl) 3)
  · exact parent_weak_field_slope_004.trans (parent_weak_field_expr_eval _ (by rfl) 4)
  · exact parent_weak_field_slope_005.trans (parent_weak_field_expr_eval _ (by rfl) 5)
  · exact parent_weak_field_slope_006.trans (parent_weak_field_expr_eval _ (by rfl) 6)
  · exact parent_weak_field_slope_007.trans (parent_weak_field_expr_eval _ (by rfl) 7)
  · exact parent_weak_field_slope_008.trans (parent_weak_field_expr_eval _ (by rfl) 8)
  · exact parent_weak_field_slope_009.trans (parent_weak_field_expr_eval _ (by rfl) 9)
  · exact parent_weak_field_slope_010.trans (parent_weak_field_expr_eval _ (by rfl) 10)
  · exact parent_weak_field_slope_011.trans (parent_weak_field_expr_eval _ (by rfl) 11)
  · exact parent_weak_field_slope_012.trans (parent_weak_field_expr_eval _ (by rfl) 12)
  · exact parent_weak_field_slope_013.trans (parent_weak_field_expr_eval _ (by rfl) 13)
  · exact parent_weak_field_slope_014.trans (parent_weak_field_expr_eval _ (by rfl) 14)
  · exact parent_weak_field_slope_015.trans (parent_weak_field_expr_eval _ (by rfl) 15)
  · exact parent_weak_field_slope_016.trans (parent_weak_field_expr_eval _ (by rfl) 16)

/-- The exact selected initial Xi contains more than the full required
2e-12 theta reserve above the actual .23 baseline. -/
theorem parent_weak_field_initial_lower (j : Fin 16) :
    (231/1000:ℝ) ≤ (parentRowFields j).getD 15 0 := by
  fin_cases j <;> simp only [parentRowFields,nativeConfiguredParentEndpoint,nativeParentEndpointCertificates,nativeParent001EndpointCertificate,nativeParent002EndpointCertificate,nativeParent003EndpointCertificate,nativeParent004EndpointCertificate,nativeParent005EndpointCertificate,nativeParent006EndpointCertificate,nativeParent007EndpointCertificate,nativeParent008EndpointCertificate,nativeParent009EndpointCertificate,nativeParent010EndpointCertificate,nativeParent011EndpointCertificate,nativeParent012EndpointCertificate,nativeParent013EndpointCertificate,nativeParent014EndpointCertificate,nativeParent015EndpointCertificate,nativeParent016EndpointCertificate,List.getD_cons_zero,List.getD_cons_succ]
  · have hq : (231/1000:ℚ) ≤ (nativeSetupParent001FieldsI.getD 15 nativeZeroInterval).lo := by decide +kernel
    exact (show (231/1000:ℝ) ≤ ((nativeSetupParent001FieldsI.getD 15 nativeZeroInterval).lo:ℝ) from by
      simpa only [Rat.cast_div,Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hq).trans (nativeSetupParent001Fields_sound 15).1
  · have hq : (231/1000:ℚ) ≤ (nativeSetupParent002FieldsI.getD 15 nativeZeroInterval).lo := by decide +kernel
    exact (show (231/1000:ℝ) ≤ ((nativeSetupParent002FieldsI.getD 15 nativeZeroInterval).lo:ℝ) from by
      simpa only [Rat.cast_div,Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hq).trans (nativeSetupParent002Fields_sound 15).1
  · have hq : (231/1000:ℚ) ≤ (nativeSetupParent003FieldsI.getD 15 nativeZeroInterval).lo := by decide +kernel
    exact (show (231/1000:ℝ) ≤ ((nativeSetupParent003FieldsI.getD 15 nativeZeroInterval).lo:ℝ) from by
      simpa only [Rat.cast_div,Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hq).trans (nativeSetupParent003Fields_sound 15).1
  · have hq : (231/1000:ℚ) ≤ (nativeSetupParent004FieldsI.getD 15 nativeZeroInterval).lo := by decide +kernel
    exact (show (231/1000:ℝ) ≤ ((nativeSetupParent004FieldsI.getD 15 nativeZeroInterval).lo:ℝ) from by
      simpa only [Rat.cast_div,Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hq).trans (nativeSetupParent004Fields_sound 15).1
  · have hq : (231/1000:ℚ) ≤ (nativeSetupParent005FieldsI.getD 15 nativeZeroInterval).lo := by decide +kernel
    exact (show (231/1000:ℝ) ≤ ((nativeSetupParent005FieldsI.getD 15 nativeZeroInterval).lo:ℝ) from by
      simpa only [Rat.cast_div,Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hq).trans (nativeSetupParent005Fields_sound 15).1
  · have hq : (231/1000:ℚ) ≤ (nativeSetupParent006FieldsI.getD 15 nativeZeroInterval).lo := by decide +kernel
    exact (show (231/1000:ℝ) ≤ ((nativeSetupParent006FieldsI.getD 15 nativeZeroInterval).lo:ℝ) from by
      simpa only [Rat.cast_div,Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hq).trans (nativeSetupParent006Fields_sound 15).1
  · have hq : (231/1000:ℚ) ≤ (nativeSetupParent007FieldsI.getD 15 nativeZeroInterval).lo := by decide +kernel
    exact (show (231/1000:ℝ) ≤ ((nativeSetupParent007FieldsI.getD 15 nativeZeroInterval).lo:ℝ) from by
      simpa only [Rat.cast_div,Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hq).trans (nativeSetupParent007Fields_sound 15).1
  · have hq : (231/1000:ℚ) ≤ (nativeSetupParent008FieldsI.getD 15 nativeZeroInterval).lo := by decide +kernel
    exact (show (231/1000:ℝ) ≤ ((nativeSetupParent008FieldsI.getD 15 nativeZeroInterval).lo:ℝ) from by
      simpa only [Rat.cast_div,Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hq).trans (nativeSetupParent008Fields_sound 15).1
  · have hq : (231/1000:ℚ) ≤ (nativeSetupParent009FieldsI.getD 15 nativeZeroInterval).lo := by decide +kernel
    exact (show (231/1000:ℝ) ≤ ((nativeSetupParent009FieldsI.getD 15 nativeZeroInterval).lo:ℝ) from by
      simpa only [Rat.cast_div,Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hq).trans (nativeSetupParent009Fields_sound 15).1
  · have hq : (231/1000:ℚ) ≤ (nativeSetupParent010FieldsI.getD 15 nativeZeroInterval).lo := by decide +kernel
    exact (show (231/1000:ℝ) ≤ ((nativeSetupParent010FieldsI.getD 15 nativeZeroInterval).lo:ℝ) from by
      simpa only [Rat.cast_div,Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hq).trans (nativeSetupParent010Fields_sound 15).1
  · have hq : (231/1000:ℚ) ≤ (nativeSetupParent011FieldsI.getD 15 nativeZeroInterval).lo := by decide +kernel
    exact (show (231/1000:ℝ) ≤ ((nativeSetupParent011FieldsI.getD 15 nativeZeroInterval).lo:ℝ) from by
      simpa only [Rat.cast_div,Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hq).trans (nativeSetupParent011Fields_sound 15).1
  · have hq : (231/1000:ℚ) ≤ (nativeSetupParent012FieldsI.getD 15 nativeZeroInterval).lo := by decide +kernel
    exact (show (231/1000:ℝ) ≤ ((nativeSetupParent012FieldsI.getD 15 nativeZeroInterval).lo:ℝ) from by
      simpa only [Rat.cast_div,Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hq).trans (nativeSetupParent012Fields_sound 15).1
  · have hq : (231/1000:ℚ) ≤ (nativeSetupParent013FieldsI.getD 15 nativeZeroInterval).lo := by decide +kernel
    exact (show (231/1000:ℝ) ≤ ((nativeSetupParent013FieldsI.getD 15 nativeZeroInterval).lo:ℝ) from by
      simpa only [Rat.cast_div,Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hq).trans (nativeSetupParent013Fields_sound 15).1
  · have hq : (231/1000:ℚ) ≤ (nativeSetupParent014FieldsI.getD 15 nativeZeroInterval).lo := by decide +kernel
    exact (show (231/1000:ℝ) ≤ ((nativeSetupParent014FieldsI.getD 15 nativeZeroInterval).lo:ℝ) from by
      simpa only [Rat.cast_div,Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hq).trans (nativeSetupParent014Fields_sound 15).1
  · have hq : (231/1000:ℚ) ≤ (nativeSetupParent015FieldsI.getD 15 nativeZeroInterval).lo := by decide +kernel
    exact (show (231/1000:ℝ) ≤ ((nativeSetupParent015FieldsI.getD 15 nativeZeroInterval).lo:ℝ) from by
      simpa only [Rat.cast_div,Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hq).trans (nativeSetupParent015Fields_sound 15).1
  · have hq : (231/1000:ℚ) ≤ (nativeSetupParent016FieldsI.getD 15 nativeZeroInterval).lo := by decide +kernel
    exact (show (231/1000:ℝ) ≤ ((nativeSetupParent016FieldsI.getD 15 nativeZeroInterval).lo:ℝ) from by
      simpa only [Rat.cast_div,Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hq).trans (nativeSetupParent016Fields_sound 15).1

end
end ASDExplicitGamma.Native
