module
public import ASDExplicitGamma.Numerics.Native.SetupParent001
public import ASDExplicitGamma.Numerics.Native.PanelValues

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open ASDExplicitGamma.Numerics

theorem nativeSetupParent001Fields_sound : ∀ i, QInterval.Contains (nativeSetupParent001FieldsI.getD i nativeZeroInterval) (nativeSetupParent001FieldsR.getD i 0) :=
  nativeSelect_sound [419, 416, 335, 385, 381, 380, 355, 345, 344, 343, 177, 143, 28, 426, 446, 445, 365] _ _ nativeSetupParent001_sound

theorem nativeSetupParent001Fields_length : nativeSetupParent001FieldsI.length = nativeSetupParent001FieldsR.length := by
  simp only [nativeSetupParent001FieldsI,nativeSetupParent001FieldsR,List.length_cons,List.length_nil]

theorem nativeSetupParent001FieldsR_length : nativeSetupParent001FieldsR.length = 17 := by
  simp only [nativeSetupParent001FieldsR,List.length_cons,List.length_nil]

theorem nativeSetupParent001Fields_lower : ∀ i : Fin 17, 0 ≤ (nativeSetupParent001FieldsI.getD i.val nativeZeroInterval).lo := by
  decide +kernel

theorem nativeSetupParent001Fields_nonneg : ∀ x ∈ nativeSetupParent001FieldsR, 0 ≤ x :=
  nativeFields_nonneg _ _ nativeSetupParent001Fields_sound (by rw [nativeSetupParent001FieldsR_length]; exact nativeSetupParent001Fields_lower)

theorem nativeSetupParent001Panel_monotone : MonotoneOn (nativePanelValue nativeSetupParent001FieldsR) (Set.Ici 0) :=
  nativePanel_monotone _ nativeSetupParent001FieldsR_length nativeSetupParent001Fields_nonneg

end ASDExplicitGamma.Numerics.Native
