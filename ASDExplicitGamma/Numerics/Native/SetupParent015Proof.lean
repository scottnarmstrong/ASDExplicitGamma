module
public import ASDExplicitGamma.Numerics.Native.SetupParent015
public import ASDExplicitGamma.Numerics.Native.PanelValues

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open ASDExplicitGamma.Numerics

theorem nativeSetupParent015Fields_sound : ∀ i, QInterval.Contains (nativeSetupParent015FieldsI.getD i nativeZeroInterval) (nativeSetupParent015FieldsR.getD i 0) :=
  nativeSelect_sound [766, 721, 323, 653, 649, 648, 343, 333, 332, 331, 171, 137, 28, 843, 863, 862, 350] _ _ nativeSetupParent015_sound

theorem nativeSetupParent015Fields_length : nativeSetupParent015FieldsI.length = nativeSetupParent015FieldsR.length := by
  simp only [nativeSetupParent015FieldsI,nativeSetupParent015FieldsR,List.length_cons,List.length_nil]

theorem nativeSetupParent015FieldsR_length : nativeSetupParent015FieldsR.length = 17 := by
  simp only [nativeSetupParent015FieldsR,List.length_cons,List.length_nil]

theorem nativeSetupParent015Fields_lower : ∀ i : Fin 17, 0 ≤ (nativeSetupParent015FieldsI.getD i.val nativeZeroInterval).lo := by
  decide +kernel

theorem nativeSetupParent015Fields_nonneg : ∀ x ∈ nativeSetupParent015FieldsR, 0 ≤ x :=
  nativeFields_nonneg _ _ nativeSetupParent015Fields_sound (by rw [nativeSetupParent015FieldsR_length]; exact nativeSetupParent015Fields_lower)

theorem nativeSetupParent015Panel_monotone : MonotoneOn (nativePanelValue nativeSetupParent015FieldsR) (Set.Ici 0) :=
  nativePanel_monotone _ nativeSetupParent015FieldsR_length nativeSetupParent015Fields_nonneg

end ASDExplicitGamma.Numerics.Native
