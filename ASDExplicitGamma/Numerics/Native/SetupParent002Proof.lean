module
public import ASDExplicitGamma.Numerics.Native.SetupParent002
public import ASDExplicitGamma.Numerics.Native.PanelValues

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open ASDExplicitGamma.Numerics

theorem nativeSetupParent002Fields_sound : ∀ i, QInterval.Contains (nativeSetupParent002FieldsI.getD i nativeZeroInterval) (nativeSetupParent002FieldsR.getD i 0) :=
  nativeSelect_sound [442, 436, 332, 402, 398, 397, 352, 342, 341, 340, 174, 140, 28, 454, 474, 473, 359] _ _ nativeSetupParent002_sound

theorem nativeSetupParent002Fields_length : nativeSetupParent002FieldsI.length = nativeSetupParent002FieldsR.length := by
  simp only [nativeSetupParent002FieldsI,nativeSetupParent002FieldsR,List.length_cons,List.length_nil]

theorem nativeSetupParent002FieldsR_length : nativeSetupParent002FieldsR.length = 17 := by
  simp only [nativeSetupParent002FieldsR,List.length_cons,List.length_nil]

theorem nativeSetupParent002Fields_lower : ∀ i : Fin 17, 0 ≤ (nativeSetupParent002FieldsI.getD i.val nativeZeroInterval).lo := by
  decide +kernel

theorem nativeSetupParent002Fields_nonneg : ∀ x ∈ nativeSetupParent002FieldsR, 0 ≤ x :=
  nativeFields_nonneg _ _ nativeSetupParent002Fields_sound (by rw [nativeSetupParent002FieldsR_length]; exact nativeSetupParent002Fields_lower)

theorem nativeSetupParent002Panel_monotone : MonotoneOn (nativePanelValue nativeSetupParent002FieldsR) (Set.Ici 0) :=
  nativePanel_monotone _ nativeSetupParent002FieldsR_length nativeSetupParent002Fields_nonneg

end ASDExplicitGamma.Numerics.Native
