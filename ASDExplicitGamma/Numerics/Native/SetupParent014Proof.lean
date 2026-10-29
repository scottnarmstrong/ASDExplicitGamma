module
public import ASDExplicitGamma.Numerics.Native.SetupParent014
public import ASDExplicitGamma.Numerics.Native.PanelValues

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open ASDExplicitGamma.Numerics

theorem nativeSetupParent014Fields_sound : ∀ i, QInterval.Contains (nativeSetupParent014FieldsI.getD i nativeZeroInterval) (nativeSetupParent014FieldsR.getD i 0) :=
  nativeSelect_sound [741, 699, 323, 633, 629, 628, 343, 333, 332, 331, 171, 137, 28, 813, 833, 832, 350] _ _ nativeSetupParent014_sound

theorem nativeSetupParent014Fields_length : nativeSetupParent014FieldsI.length = nativeSetupParent014FieldsR.length := by
  simp only [nativeSetupParent014FieldsI,nativeSetupParent014FieldsR,List.length_cons,List.length_nil]

theorem nativeSetupParent014FieldsR_length : nativeSetupParent014FieldsR.length = 17 := by
  simp only [nativeSetupParent014FieldsR,List.length_cons,List.length_nil]

theorem nativeSetupParent014Fields_lower : ∀ i : Fin 17, 0 ≤ (nativeSetupParent014FieldsI.getD i.val nativeZeroInterval).lo := by
  decide +kernel

theorem nativeSetupParent014Fields_nonneg : ∀ x ∈ nativeSetupParent014FieldsR, 0 ≤ x :=
  nativeFields_nonneg _ _ nativeSetupParent014Fields_sound (by rw [nativeSetupParent014FieldsR_length]; exact nativeSetupParent014Fields_lower)

theorem nativeSetupParent014Panel_monotone : MonotoneOn (nativePanelValue nativeSetupParent014FieldsR) (Set.Ici 0) :=
  nativePanel_monotone _ nativeSetupParent014FieldsR_length nativeSetupParent014Fields_nonneg

end ASDExplicitGamma.Numerics.Native
