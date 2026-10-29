module
public import ASDExplicitGamma.Numerics.Native.SetupParent009
public import ASDExplicitGamma.Numerics.Native.PanelValues

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open ASDExplicitGamma.Numerics

theorem nativeSetupParent009Fields_sound : ∀ i, QInterval.Contains (nativeSetupParent009FieldsI.getD i nativeZeroInterval) (nativeSetupParent009FieldsR.getD i 0) :=
  nativeSelect_sound [613, 586, 323, 533, 529, 528, 343, 333, 332, 331, 171, 137, 28, 660, 680, 679, 350] _ _ nativeSetupParent009_sound

theorem nativeSetupParent009Fields_length : nativeSetupParent009FieldsI.length = nativeSetupParent009FieldsR.length := by
  simp only [nativeSetupParent009FieldsI,nativeSetupParent009FieldsR,List.length_cons,List.length_nil]

theorem nativeSetupParent009FieldsR_length : nativeSetupParent009FieldsR.length = 17 := by
  simp only [nativeSetupParent009FieldsR,List.length_cons,List.length_nil]

theorem nativeSetupParent009Fields_lower : ∀ i : Fin 17, 0 ≤ (nativeSetupParent009FieldsI.getD i.val nativeZeroInterval).lo := by
  decide +kernel

theorem nativeSetupParent009Fields_nonneg : ∀ x ∈ nativeSetupParent009FieldsR, 0 ≤ x :=
  nativeFields_nonneg _ _ nativeSetupParent009Fields_sound (by rw [nativeSetupParent009FieldsR_length]; exact nativeSetupParent009Fields_lower)

theorem nativeSetupParent009Panel_monotone : MonotoneOn (nativePanelValue nativeSetupParent009FieldsR) (Set.Ici 0) :=
  nativePanel_monotone _ nativeSetupParent009FieldsR_length nativeSetupParent009Fields_nonneg

end ASDExplicitGamma.Numerics.Native
