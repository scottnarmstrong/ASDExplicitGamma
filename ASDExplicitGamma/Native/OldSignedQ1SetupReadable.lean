module

public import ASDExplicitGamma.Native.OldSignedQ1SetupNodes

/-! Readable exact physical fields of the unchanged q1 numerical setup. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native
noncomputable section

/-- The base shell variance is the same real value selected by the setup. -/
theorem old_signed_q1_setup_base_variance :
    oldSignedQ1SetupNode023 (nativeSetupInputReal nativeSetupQ1001A0 nativeSetupQ1001Xi0)=
      nativeSetupQ1001FieldsR.getD 0 0 := by
  rw [old_signed_q1_setup_field_00]
  norm_num only [oldSignedQ1SetupNode025,oldSignedQ1SetupNode024,Rat.cast_zero,Rat.cast_div,
    Rat.cast_ofNat,zero_div,zero_add]

/-- Positivity of the exact physical endpoint variance. -/
theorem old_signed_q1_setup_variance_nonneg : 0≤nativeSetupQ1001FieldsR.getD 0 0 := by
  rw [old_signed_q1_setup_variance]
  unfold gammaZero
  positivity

/-- Exact readable physical setup field 1. -/
theorem old_signed_q1_setup_readable_01 :
    let v := nativeSetupQ1001FieldsR.getD 0 0
    nativeSetupQ1001FieldsR.getD 1 0=v*(1/531441) := by
  intro v
  simp only [v,old_signed_q1_setup_field_01,oldSignedQ1SetupNode028,oldSignedQ1SetupNode027,oldSignedQ1SetupNode026,oldSignedQ1SetupNode024,
    old_signed_q1_setup_base_variance,Rat.cast_zero,Rat.cast_one,Rat.cast_div,
    Rat.cast_ofNat,zero_div,zero_add]

/-- Exact readable physical setup field 2. -/
theorem old_signed_q1_setup_readable_02 :
    let v := nativeSetupQ1001FieldsR.getD 0 0
    nativeSetupQ1001FieldsR.getD 2 0=Real.sqrt v+Real.sqrt (v*(1/531441)*(156/5))*(36/25)+
      Real.sqrt (v*(1/282429536481)*(46488/25))*(57/200) := by
  intro v
  simp only [v,old_signed_q1_setup_field_02,oldSignedQ1SetupNode044,oldSignedQ1SetupNode043,oldSignedQ1SetupNode042,oldSignedQ1SetupNode041,oldSignedQ1SetupNode040,oldSignedQ1SetupNode039,oldSignedQ1SetupNode038,oldSignedQ1SetupNode037,oldSignedQ1SetupNode036,oldSignedQ1SetupNode035,oldSignedQ1SetupNode034,oldSignedQ1SetupNode033,oldSignedQ1SetupNode032,oldSignedQ1SetupNode031,oldSignedQ1SetupNode030,oldSignedQ1SetupNode029,oldSignedQ1SetupNode028,oldSignedQ1SetupNode027,oldSignedQ1SetupNode026,oldSignedQ1SetupNode025,oldSignedQ1SetupNode024,
    old_signed_q1_setup_base_variance,Rat.cast_zero,Rat.cast_one,Rat.cast_div,
    Rat.cast_ofNat,zero_div,zero_add]

/-- Exact readable physical setup field 3. -/
theorem old_signed_q1_setup_readable_03 :
    let v := nativeSetupQ1001FieldsR.getD 0 0
    nativeSetupQ1001FieldsR.getD 3 0=Real.sqrt (v*(1/531441)*(156/5))*(637/1000)+
      Real.sqrt (v*(1/282429536481)*(46488/25))*(418/3125) := by
  intro v
  simp only [v,old_signed_q1_setup_field_03,oldSignedQ1SetupNode059,oldSignedQ1SetupNode058,oldSignedQ1SetupNode057,oldSignedQ1SetupNode056,oldSignedQ1SetupNode055,oldSignedQ1SetupNode041,oldSignedQ1SetupNode040,oldSignedQ1SetupNode039,oldSignedQ1SetupNode035,oldSignedQ1SetupNode034,oldSignedQ1SetupNode033,oldSignedQ1SetupNode031,oldSignedQ1SetupNode030,oldSignedQ1SetupNode029,oldSignedQ1SetupNode028,oldSignedQ1SetupNode027,oldSignedQ1SetupNode026,oldSignedQ1SetupNode024,
    old_signed_q1_setup_base_variance,Rat.cast_zero,Rat.cast_one,Rat.cast_div,
    Rat.cast_ofNat,zero_div,zero_add]

/-- Exact readable physical setup field 4. -/
theorem old_signed_q1_setup_readable_04 :
    let v := nativeSetupQ1001FieldsR.getD 0 0
    nativeSetupQ1001FieldsR.getD 4 0=(Real.sqrt 2+1)*(11/25)*Real.sqrt (v*(1/531441)*(156/5)) := by
  intro v
  simp only [v,old_signed_q1_setup_field_04,oldSignedQ1SetupNode063,oldSignedQ1SetupNode062,oldSignedQ1SetupNode061,oldSignedQ1SetupNode060,oldSignedQ1SetupNode035,oldSignedQ1SetupNode034,oldSignedQ1SetupNode033,oldSignedQ1SetupNode028,oldSignedQ1SetupNode027,oldSignedQ1SetupNode026,oldSignedQ1SetupNode024,oldSignedQ1SetupNode009,oldSignedQ1SetupNode001,oldSignedQ1SetupNode000,
    old_signed_q1_setup_base_variance,Rat.cast_zero,Rat.cast_one,Rat.cast_div,
    Rat.cast_ofNat,zero_add,div_one]

/-- Exact readable physical setup field 5. -/
theorem old_signed_q1_setup_readable_05 :
    let v := nativeSetupQ1001FieldsR.getD 0 0
    nativeSetupQ1001FieldsR.getD 5 0=Real.sqrt (v*(1/531441)*(156/5))*(11/25) := by
  intro v
  simp only [v,old_signed_q1_setup_field_05,oldSignedQ1SetupNode064,oldSignedQ1SetupNode061,oldSignedQ1SetupNode035,oldSignedQ1SetupNode034,oldSignedQ1SetupNode033,oldSignedQ1SetupNode028,oldSignedQ1SetupNode027,oldSignedQ1SetupNode026,oldSignedQ1SetupNode024,
    old_signed_q1_setup_base_variance,Rat.cast_zero,Rat.cast_one,Rat.cast_div,
    Rat.cast_ofNat,zero_div,zero_add]

/-- Exact readable physical setup field 8. -/
theorem old_signed_q1_setup_readable_08 :
    let v := nativeSetupQ1001FieldsR.getD 0 0
    nativeSetupQ1001FieldsR.getD 8 0=Real.sqrt (v+v) := by
  intro v
  simp only [v,old_signed_q1_setup_field_08,oldSignedQ1SetupNode078,oldSignedQ1SetupNode077,oldSignedQ1SetupNode071,oldSignedQ1SetupNode065,oldSignedQ1SetupNode025,oldSignedQ1SetupNode024,oldSignedQ1SetupNode000,
    old_signed_q1_setup_base_variance,Rat.cast_zero,
    Rat.cast_ofNat,zero_add,div_one]
  congr 1
  ring

/-- Exact readable physical setup field 9. -/
theorem old_signed_q1_setup_readable_09 :
    let v := nativeSetupQ1001FieldsR.getD 0 0
    nativeSetupQ1001FieldsR.getD 9 0=Real.sqrt v := by
  intro v
  simp only [v,old_signed_q1_setup_field_09,oldSignedQ1SetupNode032,oldSignedQ1SetupNode025,oldSignedQ1SetupNode024,
    old_signed_q1_setup_base_variance,Rat.cast_zero,
    zero_div,zero_add]

/-- The exact boundary coefficient keeps the full variance and both flat roots. -/
theorem old_signed_q1_setup_readable_06 :
    let v := nativeSetupQ1001FieldsR.getD 0 0
    nativeSetupQ1001FieldsR.getD 6 0=v+
      Real.sqrt (v*(1/531441)*(156/5))*(38/125)*(Real.sqrt v+Real.sqrt v*2) := by
  intro v
  simp only [old_signed_q1_setup_field_06,oldSignedQ1SetupNode076,oldSignedQ1SetupNode075,oldSignedQ1SetupNode074,oldSignedQ1SetupNode073,oldSignedQ1SetupNode072,oldSignedQ1SetupNode071,oldSignedQ1SetupNode070,oldSignedQ1SetupNode069,oldSignedQ1SetupNode068,oldSignedQ1SetupNode067,oldSignedQ1SetupNode066,oldSignedQ1SetupNode065,oldSignedQ1SetupNode035,oldSignedQ1SetupNode034,oldSignedQ1SetupNode033,oldSignedQ1SetupNode032,oldSignedQ1SetupNode028,oldSignedQ1SetupNode027,oldSignedQ1SetupNode026,oldSignedQ1SetupNode025,oldSignedQ1SetupNode024,oldSignedQ1SetupNode000,
    old_signed_q1_setup_base_variance,Rat.cast_zero,Rat.cast_one,Rat.cast_div,
    Rat.cast_ofNat,zero_add,div_one]
  change Real.sqrt (v*(v*2)/2)+Real.sqrt (v*(1/531441)*(156/5))*(38/125)*
    (Real.sqrt (v*2/2)+Real.sqrt v*2)=_
  have h1 : v*2/2=v := by ring
  have h2 : v*(v*2)/2=v^2 := by ring
  rw [h1,h2,Real.sqrt_sq old_signed_q1_setup_variance_nonneg]

/-- Both boundary signs use the same certified coefficient. -/
theorem old_signed_q1_setup_boundary_same :
    nativeSetupQ1001FieldsR.getD 7 0=nativeSetupQ1001FieldsR.getD 6 0 := by
  rw [old_signed_q1_setup_field_07,old_signed_q1_setup_field_06]

/-- The affine ybar field is the same full variance as field zero. -/
theorem old_signed_q1_setup_ybar :
    nativeSetupQ1001FieldsR.getD 16 0=nativeSetupQ1001FieldsR.getD 0 0 := by
  simp only [nativeSetupQ1001FieldsR,List.getD_cons_zero,List.getD_cons_succ]

end
end ASDExplicitGamma.Native
