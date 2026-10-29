module
public import ASDExplicitGamma.Numerics.Native.SetupParent003
public import ASDExplicitGamma.Numerics.Native.PanelValues

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open ASDExplicitGamma.Numerics

theorem nativeSetupParent003Fields_sound : ∀ i, QInterval.Contains (nativeSetupParent003FieldsI.getD i nativeZeroInterval) (nativeSetupParent003FieldsR.getD i 0) :=
  nativeSelect_sound [465, 456, 329, 419, 415, 414, 349, 339, 338, 337, 174, 140, 28, 482, 502, 501, 356] _ _ nativeSetupParent003_sound

theorem nativeSetupParent003Fields_length : nativeSetupParent003FieldsI.length = nativeSetupParent003FieldsR.length := by
  simp only [nativeSetupParent003FieldsI,nativeSetupParent003FieldsR,List.length_cons,List.length_nil]

theorem nativeSetupParent003FieldsR_length : nativeSetupParent003FieldsR.length = 17 := by
  simp only [nativeSetupParent003FieldsR,List.length_cons,List.length_nil]

theorem nativeSetupParent003Fields_lower : ∀ i : Fin 17, 0 ≤ (nativeSetupParent003FieldsI.getD i.val nativeZeroInterval).lo := by
  decide +kernel

theorem nativeSetupParent003Fields_nonneg : ∀ x ∈ nativeSetupParent003FieldsR, 0 ≤ x :=
  nativeFields_nonneg _ _ nativeSetupParent003Fields_sound (by rw [nativeSetupParent003FieldsR_length]; exact nativeSetupParent003Fields_lower)

theorem nativeSetupParent003Panel_monotone : MonotoneOn (nativePanelValue nativeSetupParent003FieldsR) (Set.Ici 0) :=
  nativePanel_monotone _ nativeSetupParent003FieldsR_length nativeSetupParent003Fields_nonneg

end ASDExplicitGamma.Numerics.Native
