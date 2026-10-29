module
public import ASDExplicitGamma.Numerics.Native.SetupParent007
public import ASDExplicitGamma.Numerics.Native.PanelValues

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open ASDExplicitGamma.Numerics

theorem nativeSetupParent007Fields_sound : ∀ i, QInterval.Contains (nativeSetupParent007FieldsI.getD i nativeZeroInterval) (nativeSetupParent007FieldsR.getD i 0) :=
  nativeSelect_sound [562, 541, 323, 493, 489, 488, 343, 333, 332, 331, 171, 137, 28, 599, 619, 618, 350] _ _ nativeSetupParent007_sound

theorem nativeSetupParent007Fields_length : nativeSetupParent007FieldsI.length = nativeSetupParent007FieldsR.length := by
  simp only [nativeSetupParent007FieldsI,nativeSetupParent007FieldsR,List.length_cons,List.length_nil]

theorem nativeSetupParent007FieldsR_length : nativeSetupParent007FieldsR.length = 17 := by
  simp only [nativeSetupParent007FieldsR,List.length_cons,List.length_nil]

theorem nativeSetupParent007Fields_lower : ∀ i : Fin 17, 0 ≤ (nativeSetupParent007FieldsI.getD i.val nativeZeroInterval).lo := by
  decide +kernel

theorem nativeSetupParent007Fields_nonneg : ∀ x ∈ nativeSetupParent007FieldsR, 0 ≤ x :=
  nativeFields_nonneg _ _ nativeSetupParent007Fields_sound (by rw [nativeSetupParent007FieldsR_length]; exact nativeSetupParent007Fields_lower)

theorem nativeSetupParent007Panel_monotone : MonotoneOn (nativePanelValue nativeSetupParent007FieldsR) (Set.Ici 0) :=
  nativePanel_monotone _ nativeSetupParent007FieldsR_length nativeSetupParent007Fields_nonneg

end ASDExplicitGamma.Numerics.Native
