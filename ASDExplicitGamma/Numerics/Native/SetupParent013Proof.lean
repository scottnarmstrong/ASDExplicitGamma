module
public import ASDExplicitGamma.Numerics.Native.SetupParent013
public import ASDExplicitGamma.Numerics.Native.PanelValues

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open ASDExplicitGamma.Numerics

theorem nativeSetupParent013Fields_sound : ∀ i, QInterval.Contains (nativeSetupParent013FieldsI.getD i nativeZeroInterval) (nativeSetupParent013FieldsR.getD i 0) :=
  nativeSelect_sound [715, 676, 323, 613, 609, 608, 343, 333, 332, 331, 171, 137, 28, 782, 802, 801, 350] _ _ nativeSetupParent013_sound

theorem nativeSetupParent013Fields_length : nativeSetupParent013FieldsI.length = nativeSetupParent013FieldsR.length := by
  simp only [nativeSetupParent013FieldsI,nativeSetupParent013FieldsR,List.length_cons,List.length_nil]

theorem nativeSetupParent013FieldsR_length : nativeSetupParent013FieldsR.length = 17 := by
  simp only [nativeSetupParent013FieldsR,List.length_cons,List.length_nil]

theorem nativeSetupParent013Fields_lower : ∀ i : Fin 17, 0 ≤ (nativeSetupParent013FieldsI.getD i.val nativeZeroInterval).lo := by
  decide +kernel

theorem nativeSetupParent013Fields_nonneg : ∀ x ∈ nativeSetupParent013FieldsR, 0 ≤ x :=
  nativeFields_nonneg _ _ nativeSetupParent013Fields_sound (by rw [nativeSetupParent013FieldsR_length]; exact nativeSetupParent013Fields_lower)

theorem nativeSetupParent013Panel_monotone : MonotoneOn (nativePanelValue nativeSetupParent013FieldsR) (Set.Ici 0) :=
  nativePanel_monotone _ nativeSetupParent013FieldsR_length nativeSetupParent013Fields_nonneg

end ASDExplicitGamma.Numerics.Native
