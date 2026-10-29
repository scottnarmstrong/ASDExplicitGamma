module
public import ASDExplicitGamma.Numerics.Native.SetupParent008
public import ASDExplicitGamma.Numerics.Native.PanelValues

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open ASDExplicitGamma.Numerics

theorem nativeSetupParent008Fields_sound : ∀ i, QInterval.Contains (nativeSetupParent008FieldsI.getD i nativeZeroInterval) (nativeSetupParent008FieldsR.getD i 0) :=
  nativeSelect_sound [588, 564, 323, 513, 509, 508, 343, 333, 332, 331, 171, 137, 28, 630, 650, 649, 350] _ _ nativeSetupParent008_sound

theorem nativeSetupParent008Fields_length : nativeSetupParent008FieldsI.length = nativeSetupParent008FieldsR.length := by
  simp only [nativeSetupParent008FieldsI,nativeSetupParent008FieldsR,List.length_cons,List.length_nil]

theorem nativeSetupParent008FieldsR_length : nativeSetupParent008FieldsR.length = 17 := by
  simp only [nativeSetupParent008FieldsR,List.length_cons,List.length_nil]

theorem nativeSetupParent008Fields_lower : ∀ i : Fin 17, 0 ≤ (nativeSetupParent008FieldsI.getD i.val nativeZeroInterval).lo := by
  decide +kernel

theorem nativeSetupParent008Fields_nonneg : ∀ x ∈ nativeSetupParent008FieldsR, 0 ≤ x :=
  nativeFields_nonneg _ _ nativeSetupParent008Fields_sound (by rw [nativeSetupParent008FieldsR_length]; exact nativeSetupParent008Fields_lower)

theorem nativeSetupParent008Panel_monotone : MonotoneOn (nativePanelValue nativeSetupParent008FieldsR) (Set.Ici 0) :=
  nativePanel_monotone _ nativeSetupParent008FieldsR_length nativeSetupParent008Fields_nonneg

end ASDExplicitGamma.Numerics.Native
