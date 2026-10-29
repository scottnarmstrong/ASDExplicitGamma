module

public import ASDExplicitGamma.Native.ParentBoundaryInverseNumericReturn
public import ASDExplicitGamma.Numerics.Native.Endpoints
public import ASDExplicitGamma.Native.BoundaryChargePanelIntegral

/-! Exact selectors for the sixteen boundary-fixed OLD parent certificates.
No source-patch identity or alternate numerical parent branch is used. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 Numerics.Native
noncomputable section

/-- The actual seventeen-field parent panel, indexed by depths one to sixteen. -/
def parentRowFields (j : Fin 16) : List ℝ :=
  (nativeConfiguredParentEndpoint j).fields

/-- The complete flat baseline from the same source program. -/
def parentRowB0 (j : Fin 16) : ℝ :=
  (nativeConfiguredParentEndpoint j).b0

/-- The exact endpoint frame multiplier, before interval rounding. -/
def parentRowFrame (j : Fin 16) : ℝ :=
  (nativeConfiguredParentEndpoint j).frame

/-- The inverse return uses the very same source setup as the panel. -/
theorem parent_row_inverse_cost_eq (j : Fin 16) :
    (nativeConfiguredParentEndpoint j).inverseCost =
      parentBoundarySetupInverseCost j := by
  fin_cases j <;> simp only [nativeConfiguredParentEndpoint, nativeParentEndpointCertificates,
    nativeParent001EndpointCertificate, nativeParent002EndpointCertificate, nativeParent003EndpointCertificate, nativeParent004EndpointCertificate, nativeParent005EndpointCertificate, nativeParent006EndpointCertificate, nativeParent007EndpointCertificate, nativeParent008EndpointCertificate, nativeParent009EndpointCertificate, nativeParent010EndpointCertificate, nativeParent011EndpointCertificate, nativeParent012EndpointCertificate, nativeParent013EndpointCertificate, nativeParent014EndpointCertificate, nativeParent015EndpointCertificate, nativeParent016EndpointCertificate,
    parentBoundarySetupInverseCost, List.getD_cons_zero, List.getD_cons_succ]

/-- The sixteen certified caps are precisely the parent rows. -/
theorem parent_row_cap_eq (j : Fin 16) :
    (nativeConfiguredParentEndpoint j).cap =
      nativeBoundaryParentCaps.getD (j.val+1) 0 := by
  fin_cases j <;> rfl

/-- All seventeen panel fields retain their checked nonnegativity. -/
theorem parent_row_fields_valid (j : Fin 16) :
    (parentRowFields j).length=17 ∧
      ∀ x ∈ parentRowFields j, 0≤x := by
  fin_cases j
  · exact ⟨nativeSetupParent001FieldsR_length, nativeSetupParent001Fields_nonneg⟩
  · exact ⟨nativeSetupParent002FieldsR_length, nativeSetupParent002Fields_nonneg⟩
  · exact ⟨nativeSetupParent003FieldsR_length, nativeSetupParent003Fields_nonneg⟩
  · exact ⟨nativeSetupParent004FieldsR_length, nativeSetupParent004Fields_nonneg⟩
  · exact ⟨nativeSetupParent005FieldsR_length, nativeSetupParent005Fields_nonneg⟩
  · exact ⟨nativeSetupParent006FieldsR_length, nativeSetupParent006Fields_nonneg⟩
  · exact ⟨nativeSetupParent007FieldsR_length, nativeSetupParent007Fields_nonneg⟩
  · exact ⟨nativeSetupParent008FieldsR_length, nativeSetupParent008Fields_nonneg⟩
  · exact ⟨nativeSetupParent009FieldsR_length, nativeSetupParent009Fields_nonneg⟩
  · exact ⟨nativeSetupParent010FieldsR_length, nativeSetupParent010Fields_nonneg⟩
  · exact ⟨nativeSetupParent011FieldsR_length, nativeSetupParent011Fields_nonneg⟩
  · exact ⟨nativeSetupParent012FieldsR_length, nativeSetupParent012Fields_nonneg⟩
  · exact ⟨nativeSetupParent013FieldsR_length, nativeSetupParent013Fields_nonneg⟩
  · exact ⟨nativeSetupParent014FieldsR_length, nativeSetupParent014Fields_nonneg⟩
  · exact ⟨nativeSetupParent015FieldsR_length, nativeSetupParent015Fields_nonneg⟩
  · exact ⟨nativeSetupParent016FieldsR_length, nativeSetupParent016Fields_nonneg⟩

/-- Exact panel integrability, before any numerical integration estimate. -/
theorem parent_row_panel_integrable (j : Fin 16) :
    IntervalIntegrable (nativePanelValue (parentRowFields j)) volume 0 1 :=
  native_boundary_panel_integrable _ (parent_row_fields_valid j).1
    (parent_row_fields_valid j).2

/-- All sixteen real boundary-fixed returns obey their certified exact caps. -/
theorem parent_row_endpoint_bound (j : Fin 16) :
    parentRowFrame j*((3/50:ℝ)+parentRowB0 j+
      (∫ t in (0:ℝ)..1, nativePanelValue (parentRowFields j) t)+
      parentBoundarySetupInverseCost j) ≤
        ((nativeBoundaryParentCaps.getD (j.val+1) 0:ℚ):ℝ) := by
  have hh := native_boundary_parent_endpoint_bound j
  rw [parent_row_cap_eq, nativePanelEndpoint, parent_row_inverse_cost_eq] at hh
  exact hh

end
end ASDExplicitGamma.Native
