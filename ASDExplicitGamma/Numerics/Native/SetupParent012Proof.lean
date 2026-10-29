module
public import ASDExplicitGamma.Numerics.Native.SetupParent012
public import ASDExplicitGamma.Numerics.Native.PanelValues

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open ASDExplicitGamma.Numerics

theorem nativeSetupParent012Fields_sound : ∀ i, QInterval.Contains (nativeSetupParent012FieldsI.getD i nativeZeroInterval) (nativeSetupParent012FieldsR.getD i 0) :=
  nativeSelect_sound [690, 654, 323, 593, 589, 588, 343, 333, 332, 331, 171, 137, 28, 752, 772, 771, 350] _ _ nativeSetupParent012_sound

theorem nativeSetupParent012Fields_length : nativeSetupParent012FieldsI.length = nativeSetupParent012FieldsR.length := by
  simp only [nativeSetupParent012FieldsI,nativeSetupParent012FieldsR,List.length_cons,List.length_nil]

theorem nativeSetupParent012FieldsR_length : nativeSetupParent012FieldsR.length = 17 := by
  simp only [nativeSetupParent012FieldsR,List.length_cons,List.length_nil]

theorem nativeSetupParent012Fields_lower : ∀ i : Fin 17, 0 ≤ (nativeSetupParent012FieldsI.getD i.val nativeZeroInterval).lo := by
  decide +kernel

theorem nativeSetupParent012Fields_nonneg : ∀ x ∈ nativeSetupParent012FieldsR, 0 ≤ x :=
  nativeFields_nonneg _ _ nativeSetupParent012Fields_sound (by rw [nativeSetupParent012FieldsR_length]; exact nativeSetupParent012Fields_lower)

theorem nativeSetupParent012Panel_monotone : MonotoneOn (nativePanelValue nativeSetupParent012FieldsR) (Set.Ici 0) :=
  nativePanel_monotone _ nativeSetupParent012FieldsR_length nativeSetupParent012Fields_nonneg

end ASDExplicitGamma.Numerics.Native
