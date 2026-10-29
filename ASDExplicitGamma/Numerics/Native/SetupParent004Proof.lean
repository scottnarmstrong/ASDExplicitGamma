module
public import ASDExplicitGamma.Numerics.Native.SetupParent004
public import ASDExplicitGamma.Numerics.Native.PanelValues

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open ASDExplicitGamma.Numerics

theorem nativeSetupParent004Fields_sound : ∀ i, QInterval.Contains (nativeSetupParent004FieldsI.getD i nativeZeroInterval) (nativeSetupParent004FieldsR.getD i 0) :=
  nativeSelect_sound [488, 476, 326, 436, 432, 431, 346, 336, 335, 334, 174, 140, 28, 510, 530, 529, 353] _ _ nativeSetupParent004_sound

theorem nativeSetupParent004Fields_length : nativeSetupParent004FieldsI.length = nativeSetupParent004FieldsR.length := by
  simp only [nativeSetupParent004FieldsI,nativeSetupParent004FieldsR,List.length_cons,List.length_nil]

theorem nativeSetupParent004FieldsR_length : nativeSetupParent004FieldsR.length = 17 := by
  simp only [nativeSetupParent004FieldsR,List.length_cons,List.length_nil]

theorem nativeSetupParent004Fields_lower : ∀ i : Fin 17, 0 ≤ (nativeSetupParent004FieldsI.getD i.val nativeZeroInterval).lo := by
  decide +kernel

theorem nativeSetupParent004Fields_nonneg : ∀ x ∈ nativeSetupParent004FieldsR, 0 ≤ x :=
  nativeFields_nonneg _ _ nativeSetupParent004Fields_sound (by rw [nativeSetupParent004FieldsR_length]; exact nativeSetupParent004Fields_lower)

theorem nativeSetupParent004Panel_monotone : MonotoneOn (nativePanelValue nativeSetupParent004FieldsR) (Set.Ici 0) :=
  nativePanel_monotone _ nativeSetupParent004FieldsR_length nativeSetupParent004Fields_nonneg

end ASDExplicitGamma.Numerics.Native
