module
public import ASDExplicitGamma.Numerics.Native.SetupParent016
public import ASDExplicitGamma.Numerics.Native.PanelValues

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open ASDExplicitGamma.Numerics

theorem nativeSetupParent016Fields_sound : ∀ i, QInterval.Contains (nativeSetupParent016FieldsI.getD i nativeZeroInterval) (nativeSetupParent016FieldsR.getD i 0) :=
  nativeSelect_sound [792, 744, 323, 673, 669, 668, 343, 333, 332, 331, 171, 137, 28, 874, 894, 893, 350] _ _ nativeSetupParent016_sound

theorem nativeSetupParent016Fields_length : nativeSetupParent016FieldsI.length = nativeSetupParent016FieldsR.length := by
  simp only [nativeSetupParent016FieldsI,nativeSetupParent016FieldsR,List.length_cons,List.length_nil]

theorem nativeSetupParent016FieldsR_length : nativeSetupParent016FieldsR.length = 17 := by
  simp only [nativeSetupParent016FieldsR,List.length_cons,List.length_nil]

theorem nativeSetupParent016Fields_lower : ∀ i : Fin 17, 0 ≤ (nativeSetupParent016FieldsI.getD i.val nativeZeroInterval).lo := by
  decide +kernel

theorem nativeSetupParent016Fields_nonneg : ∀ x ∈ nativeSetupParent016FieldsR, 0 ≤ x :=
  nativeFields_nonneg _ _ nativeSetupParent016Fields_sound (by rw [nativeSetupParent016FieldsR_length]; exact nativeSetupParent016Fields_lower)

theorem nativeSetupParent016Panel_monotone : MonotoneOn (nativePanelValue nativeSetupParent016FieldsR) (Set.Ici 0) :=
  nativePanel_monotone _ nativeSetupParent016FieldsR_length nativeSetupParent016Fields_nonneg

end ASDExplicitGamma.Numerics.Native
