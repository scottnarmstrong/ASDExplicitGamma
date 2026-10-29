module
public import ASDExplicitGamma.Numerics.Native.SetupParent011
public import ASDExplicitGamma.Numerics.Native.PanelValues

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open ASDExplicitGamma.Numerics

theorem nativeSetupParent011Fields_sound : ∀ i, QInterval.Contains (nativeSetupParent011FieldsI.getD i nativeZeroInterval) (nativeSetupParent011FieldsR.getD i 0) :=
  nativeSelect_sound [664, 631, 323, 573, 569, 568, 343, 333, 332, 331, 171, 137, 28, 721, 741, 740, 350] _ _ nativeSetupParent011_sound

theorem nativeSetupParent011Fields_length : nativeSetupParent011FieldsI.length = nativeSetupParent011FieldsR.length := by
  simp only [nativeSetupParent011FieldsI,nativeSetupParent011FieldsR,List.length_cons,List.length_nil]

theorem nativeSetupParent011FieldsR_length : nativeSetupParent011FieldsR.length = 17 := by
  simp only [nativeSetupParent011FieldsR,List.length_cons,List.length_nil]

theorem nativeSetupParent011Fields_lower : ∀ i : Fin 17, 0 ≤ (nativeSetupParent011FieldsI.getD i.val nativeZeroInterval).lo := by
  decide +kernel

theorem nativeSetupParent011Fields_nonneg : ∀ x ∈ nativeSetupParent011FieldsR, 0 ≤ x :=
  nativeFields_nonneg _ _ nativeSetupParent011Fields_sound (by rw [nativeSetupParent011FieldsR_length]; exact nativeSetupParent011Fields_lower)

theorem nativeSetupParent011Panel_monotone : MonotoneOn (nativePanelValue nativeSetupParent011FieldsR) (Set.Ici 0) :=
  nativePanel_monotone _ nativeSetupParent011FieldsR_length nativeSetupParent011Fields_nonneg

end ASDExplicitGamma.Numerics.Native
