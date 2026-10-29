module
public import ASDExplicitGamma.Numerics.Native.SetupParent010
public import ASDExplicitGamma.Numerics.Native.PanelValues

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open ASDExplicitGamma.Numerics

theorem nativeSetupParent010Fields_sound : ∀ i, QInterval.Contains (nativeSetupParent010FieldsI.getD i nativeZeroInterval) (nativeSetupParent010FieldsR.getD i 0) :=
  nativeSelect_sound [639, 609, 323, 553, 549, 548, 343, 333, 332, 331, 171, 137, 28, 691, 711, 710, 350] _ _ nativeSetupParent010_sound

theorem nativeSetupParent010Fields_length : nativeSetupParent010FieldsI.length = nativeSetupParent010FieldsR.length := by
  simp only [nativeSetupParent010FieldsI,nativeSetupParent010FieldsR,List.length_cons,List.length_nil]

theorem nativeSetupParent010FieldsR_length : nativeSetupParent010FieldsR.length = 17 := by
  simp only [nativeSetupParent010FieldsR,List.length_cons,List.length_nil]

theorem nativeSetupParent010Fields_lower : ∀ i : Fin 17, 0 ≤ (nativeSetupParent010FieldsI.getD i.val nativeZeroInterval).lo := by
  decide +kernel

theorem nativeSetupParent010Fields_nonneg : ∀ x ∈ nativeSetupParent010FieldsR, 0 ≤ x :=
  nativeFields_nonneg _ _ nativeSetupParent010Fields_sound (by rw [nativeSetupParent010FieldsR_length]; exact nativeSetupParent010Fields_lower)

theorem nativeSetupParent010Panel_monotone : MonotoneOn (nativePanelValue nativeSetupParent010FieldsR) (Set.Ici 0) :=
  nativePanel_monotone _ nativeSetupParent010FieldsR_length nativeSetupParent010Fields_nonneg

end ASDExplicitGamma.Numerics.Native
