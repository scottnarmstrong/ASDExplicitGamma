module
public import ASDExplicitGamma.Numerics.Native.SetupParent006
public import ASDExplicitGamma.Numerics.Native.PanelValues

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open ASDExplicitGamma.Numerics

theorem nativeSetupParent006Fields_sound : ∀ i, QInterval.Contains (nativeSetupParent006FieldsI.getD i nativeZeroInterval) (nativeSetupParent006FieldsR.getD i 0) :=
  nativeSelect_sound [537, 519, 323, 473, 469, 468, 343, 333, 332, 331, 171, 137, 28, 569, 589, 588, 350] _ _ nativeSetupParent006_sound

theorem nativeSetupParent006Fields_length : nativeSetupParent006FieldsI.length = nativeSetupParent006FieldsR.length := by
  simp only [nativeSetupParent006FieldsI,nativeSetupParent006FieldsR,List.length_cons,List.length_nil]

theorem nativeSetupParent006FieldsR_length : nativeSetupParent006FieldsR.length = 17 := by
  simp only [nativeSetupParent006FieldsR,List.length_cons,List.length_nil]

theorem nativeSetupParent006Fields_lower : ∀ i : Fin 17, 0 ≤ (nativeSetupParent006FieldsI.getD i.val nativeZeroInterval).lo := by
  decide +kernel

theorem nativeSetupParent006Fields_nonneg : ∀ x ∈ nativeSetupParent006FieldsR, 0 ≤ x :=
  nativeFields_nonneg _ _ nativeSetupParent006Fields_sound (by rw [nativeSetupParent006FieldsR_length]; exact nativeSetupParent006Fields_lower)

theorem nativeSetupParent006Panel_monotone : MonotoneOn (nativePanelValue nativeSetupParent006FieldsR) (Set.Ici 0) :=
  nativePanel_monotone _ nativeSetupParent006FieldsR_length nativeSetupParent006Fields_nonneg

end ASDExplicitGamma.Numerics.Native
