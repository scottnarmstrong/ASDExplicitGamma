module
public import ASDExplicitGamma.Numerics.Native.SetupQ1001
public import ASDExplicitGamma.Numerics.Native.PanelValues

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open ASDExplicitGamma.Numerics

theorem nativeSetupQ1001Fields_sound : ∀ i, QInterval.Contains (nativeSetupQ1001FieldsI.getD i nativeZeroInterval) (nativeSetupQ1001FieldsR.getD i 0) :=
  nativeSelect_sound [388, 385, 369, 354, 350, 349, 337, 337, 335, 381, 177, 143, 28, 395, 415, 414, 388] _ _ nativeSetupQ1001_sound

theorem nativeSetupQ1001Fields_length : nativeSetupQ1001FieldsI.length = nativeSetupQ1001FieldsR.length := by
  simp only [nativeSetupQ1001FieldsI,nativeSetupQ1001FieldsR,List.length_cons,List.length_nil]

theorem nativeSetupQ1001FieldsR_length : nativeSetupQ1001FieldsR.length = 17 := by
  simp only [nativeSetupQ1001FieldsR,List.length_cons,List.length_nil]

theorem nativeSetupQ1001Fields_lower : ∀ i : Fin 17, 0 ≤ (nativeSetupQ1001FieldsI.getD i.val nativeZeroInterval).lo := by
  decide +kernel

theorem nativeSetupQ1001Fields_nonneg : ∀ x ∈ nativeSetupQ1001FieldsR, 0 ≤ x :=
  nativeFields_nonneg _ _ nativeSetupQ1001Fields_sound (by rw [nativeSetupQ1001FieldsR_length]; exact nativeSetupQ1001Fields_lower)

theorem nativeSetupQ1001Panel_monotone : MonotoneOn (nativePanelValue nativeSetupQ1001FieldsR) (Set.Ici 0) :=
  nativePanel_monotone _ nativeSetupQ1001FieldsR_length nativeSetupQ1001Fields_nonneg

end ASDExplicitGamma.Numerics.Native
