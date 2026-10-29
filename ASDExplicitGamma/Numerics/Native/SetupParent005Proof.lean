module
public import ASDExplicitGamma.Numerics.Native.SetupParent005
public import ASDExplicitGamma.Numerics.Native.PanelValues

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open ASDExplicitGamma.Numerics

theorem nativeSetupParent005Fields_sound : ∀ i, QInterval.Contains (nativeSetupParent005FieldsI.getD i nativeZeroInterval) (nativeSetupParent005FieldsR.getD i 0) :=
  nativeSelect_sound [511, 496, 323, 453, 449, 448, 343, 333, 332, 331, 171, 137, 28, 538, 558, 557, 350] _ _ nativeSetupParent005_sound

theorem nativeSetupParent005Fields_length : nativeSetupParent005FieldsI.length = nativeSetupParent005FieldsR.length := by
  simp only [nativeSetupParent005FieldsI,nativeSetupParent005FieldsR,List.length_cons,List.length_nil]

theorem nativeSetupParent005FieldsR_length : nativeSetupParent005FieldsR.length = 17 := by
  simp only [nativeSetupParent005FieldsR,List.length_cons,List.length_nil]

theorem nativeSetupParent005Fields_lower : ∀ i : Fin 17, 0 ≤ (nativeSetupParent005FieldsI.getD i.val nativeZeroInterval).lo := by
  decide +kernel

theorem nativeSetupParent005Fields_nonneg : ∀ x ∈ nativeSetupParent005FieldsR, 0 ≤ x :=
  nativeFields_nonneg _ _ nativeSetupParent005Fields_sound (by rw [nativeSetupParent005FieldsR_length]; exact nativeSetupParent005Fields_lower)

theorem nativeSetupParent005Panel_monotone : MonotoneOn (nativePanelValue nativeSetupParent005FieldsR) (Set.Ici 0) :=
  nativePanel_monotone _ nativeSetupParent005FieldsR_length nativeSetupParent005Fields_nonneg

end ASDExplicitGamma.Numerics.Native
